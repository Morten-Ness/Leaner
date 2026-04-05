import Mathlib

variable {C : Type*} [Category* C] [Abelian C]

variable {K L : CochainComplex C ℤ} (f : K ⟶ L)

variable [EnoughInjectives C]

variable (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁)

theorem degreewiseEpiWithInjectiveKernel_π :
    degreewiseEpiWithInjectiveKernel (π K L n₁) := by
  intro q
  rw [Abelian.epiWithInjectiveKernel_iff]
  exact ⟨(S K n₁).X q, inferInstance, (biprod.inl : _ ⟶ mid K L n₁).f q, by simp,
    ⟨{ r := (biprod.fst : mid K L n₁ ⟶ _).f q, s := (biprod.inr : _ ⟶ mid K L n₁).f q }⟩⟩

