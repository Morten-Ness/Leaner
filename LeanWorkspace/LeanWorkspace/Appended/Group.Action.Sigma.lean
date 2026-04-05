import Mathlib

section

variable {ι : Type*} {M N : Type*} {α : ι → Type*}

variable [∀ i, SMul M (α i)] [∀ i, SMul N (α i)] (a : M) (i : ι) (b : α i) (x : Σ i, α i)

theorem FaithfulSMul' [FaithfulSMul M (α i)] : FaithfulSMul M (Σ i, α i) := ⟨fun h => eq_of_smul_eq_smul fun a : α i => heq_iff_eq.1 (Sigma.ext_iff.1 <| h <| Sigma.mk i a).2⟩

end
