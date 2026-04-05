import Mathlib

section

variable {ι M N : Type*} {α β γ : ι → Type*} (i : ι)

theorem faithfulSMul_at [∀ i, SMul M (α i)] [∀ i, Nonempty (α i)] (i : ι) [FaithfulSMul M (α i)] :
    FaithfulSMul M (∀ i, α i) where
  eq_of_smul_eq_smul h := eq_of_smul_eq_smul fun a : α i => by
    classical
    simpa using
      congr_fun (h <| Function.update (fun j => Classical.choice (‹∀ i, Nonempty (α i)› j)) i a) i

end

section

variable {ι M N : Type*} {α β γ : ι → Type*} (i : ι)

theorem piecewise_smul [∀ i, SMul M (α i)] (s : Set ι) [∀ i, Decidable (i ∈ s)]
    (c : M) (f₁ g₁ : ∀ i, α i) : s.piecewise (c • f₁) (c • g₁) = c • s.piecewise f₁ g₁ := s.piecewise_op (δ' := α) f₁ _ fun _ ↦ (c • ·)

end
