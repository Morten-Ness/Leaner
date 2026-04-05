import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

theorem inf_limZero {f g : CauSeq α abs} (hf : CauSeq.LimZero f) (hg : CauSeq.LimZero g) : CauSeq.LimZero (f ⊓ g)
  | ε, ε0 =>
    (exists_forall_ge_and (hf _ ε0) (hg _ ε0)).imp fun _ H j ij => by
      let ⟨H₁, H₂⟩ := H _ ij
      rw [abs_lt] at H₁ H₂ ⊢
      exact ⟨lt_inf_iff.mpr ⟨H₁.1, H₂.1⟩, inf_lt_iff.mpr (Or.inl H₁.2)⟩

