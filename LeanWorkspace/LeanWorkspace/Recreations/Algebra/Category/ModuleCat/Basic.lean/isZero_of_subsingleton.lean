import Mathlib

variable (R : Type u) [Ring R]

theorem isZero_of_subsingleton (M : ModuleCat R) [Subsingleton M] : IsZero M where
  unique_to X := ⟨⟨⟨ofHom (0 : M →ₗ[R] X)⟩, fun f => by
    ext x
    rw [Subsingleton.elim x (0 : M)]
    simp⟩⟩
  unique_from X := ⟨⟨⟨ofHom (0 : X →ₗ[R] M)⟩, fun f => by
    ext x
    subsingleton⟩⟩

