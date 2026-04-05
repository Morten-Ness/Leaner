import Mathlib

variable {k G : Type*}

variable [Semiring k]

variable [Mul G] [SMulZeroClass G k]

set_option backward.privateInPublic true in
private def add :
    SkewMonoidAlgebra k G → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

set_option backward.privateInPublic true in
private def smul {S : Type*} [SMulZeroClass S k] :
    S → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | s, ⟨b⟩ => ⟨s • b⟩

theorem coeff_mul_antidiagonal_of_finset (f g : SkewMonoidAlgebra k G) (x : G)
    (s : Finset (G × G)) (hs : ∀ {p : G × G}, p ∈ s ↔ p.1 * p.2 = x) :
    (f * g).coeff x = ∑ p ∈ s, f.coeff p.1 * p.1 • g.coeff p.2 := by
  classical
  let F : G × G → k := fun p ↦ if p.1 * p.2 = x then f.coeff p.1 * p.1 • g.coeff p.2 else 0
  calc
    (f * g).coeff x = ∑ a₁ ∈ f.support, ∑ a₂ ∈ g.support, F (a₁, a₂) := SkewMonoidAlgebra.coeff_mul f g x
    _ = ∑ p ∈ f.support ×ˢ g.support, F p := by rw [← Finset.sum_product _ _ _]
    _ = ∑ p ∈ (f.support ×ˢ g.support).filter fun p : G × G ↦ p.1 * p.2 = x,
      f.coeff p.1 * p.1 • g.coeff p.2 := (Finset.sum_filter _ _).symm
    _ = ∑ p ∈ s.filter fun p : G × G ↦ p.1 ∈ f.support ∧ p.2 ∈ g.support,
      f.coeff p.1 * p.1 • g.coeff p.2 :=
      (Finset.sum_congr (by SkewMonoidAlgebra.ext; simp [Finset.mem_filter, Finset.mem_product, hs, and_comm])
        fun _ _ ↦ rfl)
    _ = ∑ p ∈ s, f.coeff p.1 * p.1 • g.coeff p.2 :=
      Finset.sum_subset (Finset.filter_subset _ _) fun p hps hp ↦ by
        simp only [Finset.mem_filter, SkewMonoidAlgebra.mem_support_iff, not_and, Classical.not_not] at hp ⊢
        by_cases h1 : f.coeff p.1 = 0 <;> simp_all

