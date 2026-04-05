import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem closure_closure_coe_preimage {s : Set M} :
    closure ((Subtype.val : closure s → M) ⁻¹' s) = ⊤ := eq_top_iff.2 fun x _ ↦ Subtype.recOn x fun _ hx' ↦
    closure_induction (fun _ h ↦ subset_closure h) (fun _ _ _ _ ↦ mul_mem) hx'

