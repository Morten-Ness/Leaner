import Mathlib

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable {v : ι → M}

variable [Ring R] [CommRing R₂] [AddCommGroup M]

variable [Module R M] [Module R₂ M]

variable {x y : M}

variable (b : Basis ι R M)

theorem coe_mkFinConsOfLE {n : ℕ} {N O : Submodule R M} (y : M) (yO : y ∈ O) (b : Module.Basis (Fin n) R N)
    (hNO : N ≤ O) (hli : ∀ (c : R), ∀ x ∈ N, c • y + x = 0 → c = 0)
    (hsp : ∀ z ∈ O, ∃ c : R, z + c • y ∈ N) :
    (Module.Basis.mkFinConsOfLE y yO b hNO hli hsp : Fin (n + 1) → O) =
      Fin.cons ⟨y, yO⟩ (Submodule.inclusion hNO ∘ b) := Module.Basis.coe_mkFinCons _ _ _ _

