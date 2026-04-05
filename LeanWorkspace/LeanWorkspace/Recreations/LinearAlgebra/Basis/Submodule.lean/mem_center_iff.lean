import Mathlib

variable {ι ι' R R₂ M M' : Type*}

variable {v : ι → M}

variable [Ring R] [CommRing R₂] [AddCommGroup M]

variable [Module R M] [Module R₂ M]

variable {x y : M}

variable (b : Basis ι R M)

theorem mem_center_iff {A}
    [Semiring R] [NonUnitalNonAssocSemiring A]
    [Module R A] [SMulCommClass R A A] [SMulCommClass R R A] [IsScalarTower R A A]
    (b : Module.Basis ι R A) {z : A} :
    z ∈ Set.center A ↔
      (∀ i, Commute (b i) z) ∧ ∀ i j,
        z * (b i * b j) = (z * b i) * b j
          ∧ (b i * b j) * z = b i * (b j * z) := by
  constructor
  · intro h
    constructor
    · intro i
      apply (h.1 (b i)).symm
    · intros
      exact ⟨h.2 _ _, h.3 _ _⟩
  · intro h
    rw [center, mem_setOf_eq]
    constructor
    case comm =>
      intro y
      rw [← b.linearCombination_repr y, linearCombination_apply, sum, commute_iff_eq,
        Finset.sum_mul, Finset.mul_sum]
      simp_rw [mul_smul_comm, smul_mul_assoc, (h.1 _).eq]
    case left_assoc =>
      intro c d
      rw [← b.linearCombination_repr c, ← b.linearCombination_repr d, linearCombination_apply,
          linearCombination_apply, sum, sum, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum,
          Finset.mul_sum]
      simp_rw [smul_mul_assoc, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, Finset.mul_sum,
        Finset.smul_sum, smul_mul_assoc, mul_smul_comm, (h.2 _ _).1,
        (@SMulCommClass.smul_comm R R A)]
      rw [Finset.sum_comm]
    case right_assoc =>
      intro c d
      rw [← b.linearCombination_repr c, ← b.linearCombination_repr d, linearCombination_apply,
          linearCombination_apply, sum, Finsupp.sum, Finset.sum_mul]
      simp_rw [smul_mul_assoc, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, Finset.mul_sum,
               Finset.smul_sum, smul_mul_assoc, mul_smul_comm, Finset.sum_mul, smul_mul_assoc,
               (h.2 _ _).2]

