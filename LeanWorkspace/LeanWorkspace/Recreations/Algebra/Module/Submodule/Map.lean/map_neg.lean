import Mathlib

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}

variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable [Ring R] [AddCommGroup M] [Module R M] (p : Submodule R M)

variable [AddCommGroup M₂] [Module R M₂]

theorem map_neg (f : M →ₗ[R] M₂) : Submodule.map (-f) p = Submodule.map f p := ext fun _ =>
    ⟨fun ⟨x, hx, hy⟩ => hy ▸ ⟨-x, show -x ∈ p from neg_mem hx, map_neg f x⟩, fun ⟨x, hx, hy⟩ =>
      hy ▸ ⟨-x, show -x ∈ p from neg_mem hx, (map_neg (-f) _).trans (neg_neg (f x))⟩⟩

