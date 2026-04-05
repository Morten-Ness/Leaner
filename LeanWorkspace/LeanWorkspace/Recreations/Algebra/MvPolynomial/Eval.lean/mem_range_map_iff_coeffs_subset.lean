import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable (f : R →+* S₁)

theorem mem_range_map_iff_coeffs_subset {f : R →+* S₁} {x : MvPolynomial σ S₁} :
    x ∈ Set.range (MvPolynomial.map f) ↔ (x.coeffs : Set _) ⊆ .range f := by
  classical
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · obtain ⟨p, rfl⟩ := hx
    exact subset_trans (MvPolynomial.coe_coeffs_map f p) (by simp)
  · induction x using induction_on'' with
    | C a =>
      by_cases h : a = 0
      · subst h
        exact ⟨0, by simp⟩
      · simp only [coeffs_C, h, reduceIte, Finset.coe_singleton, Set.singleton_subset_iff] at hx
        obtain ⟨b, rfl⟩ := hx
        exact ⟨C b, by simp⟩
    | mul_X p n ih =>
      rw [coeffs_mul_X] at hx
      obtain ⟨q, rfl⟩ := ih hx
      exact ⟨q * X n, by simp⟩
    | monomial_add a s p ha hs hp ih =>
      rw [coeffs_add (disjoint_support_monomial ha hs)] at hx
      simp only [Finset.coe_union, Set.union_subset_iff] at hx
      obtain ⟨q, hq⟩ := ih hx.1
      obtain ⟨u, hu⟩ := hp hx.2
      exact ⟨q + u, by simp [hq, hu]⟩

