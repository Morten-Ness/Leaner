import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Ring β]
  {abv : β → α} [IsAbsoluteValue abv] {f g : ℕ → β}

theorem mul (hf : IsCauSeq abv f) (hg : IsCauSeq abv g) : IsCauSeq abv (f * g) := fun _ ε0 =>
  let ⟨_, _, hF⟩ := IsCauSeq.bounded' hf 0
  let ⟨_, _, hG⟩ := IsCauSeq.bounded' hg 0
  let ⟨_, δ0, Hδ⟩ := rat_mul_continuous_lemma abv ε0
  let ⟨i, H⟩ := exists_forall_ge_and (IsCauSeq.cauchy₃ hf δ0) (IsCauSeq.cauchy₃ hg δ0)
  ⟨i, fun j ij =>
    let ⟨H₁, H₂⟩ := H _ le_rfl
    Hδ (hF j) (hG i) (H₁ _ ij) (H₂ _ ij)⟩

