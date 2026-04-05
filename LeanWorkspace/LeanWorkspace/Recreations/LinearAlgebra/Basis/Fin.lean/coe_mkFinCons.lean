import Mathlib

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable {v : ι → M}

variable [Ring R] [CommRing R₂] [AddCommGroup M]

variable [Module R M] [Module R₂ M]

variable {x y : M}

variable (b : Basis ι R M)

theorem coe_mkFinCons {n : ℕ} {N : Submodule R M} (y : M) (b : Module.Basis (Fin n) R N)
    (hli : ∀ (c : R), ∀ x ∈ N, c • y + x = 0 → c = 0) (hsp : ∀ z : M, ∃ c : R, z + c • y ∈ N) :
    (Module.Basis.mkFinCons y b hli hsp : Fin (n + 1) → M) = Fin.cons y ((↑) ∘ b) := by
  unfold Module.Basis.mkFinCons
  exact coe_mk (v := Fin.cons y (N.subtype ∘ b)) _ _

