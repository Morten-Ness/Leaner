import Mathlib

open scoped Classical

variable {ι M N : Type*} {α β γ : ι → Type*} (i : ι)

theorem faithfulSMul_at [∀ i, SMul M (α i)] [∀ i, Nonempty (α i)] (i : ι) [FaithfulSMul M (α i)] :
    FaithfulSMul M (∀ i, α i) where
  eq_of_smul_eq_smul h := by
    classical
    apply FaithfulSMul.eq_of_smul_eq_smul (α := α i)
    intro x
    let y : ∀ j, α j := Function.update (fun j => Classical.choice (inferInstance : Nonempty (α j))) i x
    have hy := congrFun (h y) i
    simpa [y] using hy
