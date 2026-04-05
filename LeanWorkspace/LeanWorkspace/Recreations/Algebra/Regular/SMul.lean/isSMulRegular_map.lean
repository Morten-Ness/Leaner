import Mathlib

variable {R S : Type*} (M : Type*) {a b : R} {s : S}

theorem isSMulRegular_map [SMul R M] [SMul S M] (f : R → S) (smul : ∀ m : M, f a • m = a • m) :
    IsSMulRegular M (f a) ↔ IsSMulRegular M a := by simp [IsSMulRegular, smul]

protected alias ⟨IsSMulRegular.of_map, IsSMulRegular.map⟩ := isSMulRegular_map

