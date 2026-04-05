import Mathlib

theorem _root_.AlgHomClass.unitization_injective {F R S A : Type*} [Field R] [Ring A]
    [Algebra R A] [SetLike S A] [hSA : NonUnitalSubringClass S A] [hSRA : SMulMemClass S R A]
    (s : S) (h1 : 1 ∉ s) [FunLike F (Unitization R s) A] [AlgHomClass F R (Unitization R s) A]
    (f : F) (hf : ∀ x : s, f x = x) : Function.Injective f := by
  refine AlgHomClass.unitization_injective' s (fun r hr hr' ↦ ?_) f hf
  rw [Algebra.algebraMap_eq_smul_one] at hr'
  exact h1 <| inv_smul_smul₀ hr (1 : A) ▸ SMulMemClass.smul_mem r⁻¹ hr'

