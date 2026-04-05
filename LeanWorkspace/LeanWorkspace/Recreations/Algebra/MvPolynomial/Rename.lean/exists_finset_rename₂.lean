import Mathlib

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

theorem exists_finset_rename₂ (p₁ p₂ : MvPolynomial σ R) :
    ∃ (s : Finset σ) (q₁ q₂ : MvPolynomial s R), p₁ = MvPolynomial.rename (↑) q₁ ∧ p₂ = MvPolynomial.rename (↑) q₂ := by
  obtain ⟨s₁, q₁, rfl⟩ := MvPolynomial.exists_finset_rename p₁
  obtain ⟨s₂, q₂, rfl⟩ := MvPolynomial.exists_finset_rename p₂
  classical
    use s₁ ∪ s₂
    use MvPolynomial.rename (fun x ↦ ⟨x, Finset.subset_union_left x.2⟩) q₁
    use MvPolynomial.rename (fun x ↦ ⟨x, Finset.subset_union_right x.2⟩) q₂
    constructor <;> simp [Function.comp_def]

