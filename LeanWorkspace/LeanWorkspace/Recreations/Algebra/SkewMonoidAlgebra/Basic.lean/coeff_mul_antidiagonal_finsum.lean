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

theorem coeff_mul_antidiagonal_finsum (f g : SkewMonoidAlgebra k G) (x : G) :
    (f * g).coeff x = ∑ᶠ p ∈ {p : G × G | p.1 * p.2 = x}, f.coeff p.1 * p.1 • g.coeff p.2 := by
  have : ({p : G × G | p.1 * p.2 = x}
      ∩ Function.support fun p ↦ f.coeff p.1 * p.1 • g.coeff p.2).Finite := by
    apply Set.Finite.inter_of_right
    apply Set.Finite.subset (Finset.finite_toSet ((f.support).product (g.support)))
    aesop
  rw [← finsum_mem_inter_support, finsum_mem_eq_finite_toFinset_sum _ this]
  classical
  let s := Set.Finite.toFinset (s := ({p : G × G | p.1 * p.2 = x}
    ∩ Function.support fun p ↦ f.coeff p.1 * p.1 • g.coeff p.2)) this
  let F : G × G → k := fun p ↦ if p.1 * p.2 = x then f.coeff p.1 * p.1 • g.coeff p.2 else 0
  calc
    (f * g).coeff x = ∑ a₁ ∈ f.support, ∑ a₂ ∈ g.support, F (a₁, a₂) := SkewMonoidAlgebra.coeff_mul f g x
    _ = ∑ p ∈ f.support ×ˢ g.support, F p := by rw [← Finset.sum_product _ _ _]
    _ = ∑ p ∈ (f.support ×ˢ g.support).filter fun p : G × G ↦ p.1 * p.2 = x,
      f.coeff p.1 * p.1 • g.coeff p.2 := (Finset.sum_filter _ _).symm
    _ = ∑ p ∈ s.filter fun p : G × G ↦ p.1 ∈ f.support ∧ p.2 ∈ g.support,
      f.coeff p.1 * p.1 • g.coeff p.2 := by
        apply Finset.sum_congr_of_eq_on_inter <;> aesop
    _ = ∑ p ∈ s, f.coeff p.1 * p.1 • g.coeff p.2 :=
      Finset.sum_subset (Finset.filter_subset _ _) fun p hps hp ↦ by
        simp only [Finset.mem_filter, SkewMonoidAlgebra.mem_support_iff, not_and, Classical.not_not] at hp ⊢
        by_cases h1 : f.coeff p.1 = 0 <;> simp_all

