import Mathlib

section

variable {M : Type*} {S T : Set M}

variable [Mul M]

theorem center_prod {N : Type*} [Mul N] :
    Set.center (M × N) = Set.center M ×ˢ Set.center N := by
  aesop (add simp [Prod.forall, forall_and, commute_iff_eq, isMulCentral_iff, Set.mem_center_iff])

end

section

variable {M : Type*} {S T : Set M}

variable [Mul M]

theorem centralizer_centralizer_centralizer (S : Set M) :
    S.centralizer.centralizer.centralizer = S.centralizer := by
  refine Set.Subset.antisymm ?_ Set.subset_centralizer_centralizer
  exact fun x hx y hy ↦ hx y <| Set.subset_centralizer_centralizer hy

end

section

variable {M : Type*} {S T : Set M}

variable [Mul M]

theorem centralizer_centralizer_comm_of_comm (h_comm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) :
    ∀ x ∈ S.centralizer.centralizer, ∀ y ∈ S.centralizer.centralizer, x * y = y * x := fun _ h₁ _ h₂ ↦ h₂ _ fun _ h₃ ↦ h₁ _ fun _ h₄ ↦ h_comm _ h₄ _ h₃

end

section

variable {M : Type*} {S T : Set M}

variable [Semigroup M] {a b : M}

theorem centralizer_eq_top_iff_subset : Set.centralizer S = Set.univ ↔ S ⊆ Set.center M := eq_top_iff.trans <| ⟨
    fun h _ hx ↦ Semigroup.mem_center_iff.mpr fun _ ↦ by rw [h trivial _ hx],
    fun h _ _ _ hm ↦ (h hm).comm _⟩

end

section

variable {M : Type*} {S T : Set M}

variable [DivisionMonoid M] {a b : M}

theorem div_mem_center (ha : a ∈ Set.center M) (hb : b ∈ Set.center M) : a / b ∈ Set.center M := by
  rw [div_eq_mul_inv]
  exact Set.mul_mem_center ha (Set.inv_mem_center hb)

end

section

variable {M : Type*} {S T : Set M}

variable [Group M] {a b : M}

theorem div_mem_centralizer (ha : a ∈ Set.centralizer S) (hb : b ∈ Set.centralizer S) :
    a / b ∈ Set.centralizer S := by
  simpa only [div_eq_mul_inv] using Set.mul_mem_centralizer ha (Set.inv_mem_centralizer hb)

end

section

variable {M : Type*} {S T : Set M}

variable [Monoid M]

theorem invOf_mem_center {a : M} [Invertible a] (ha : a ∈ Set.center M) : ⅟a ∈ Set.center M := by
  rw [Semigroup.mem_center_iff] at *
  exact (Commute.invOf_right <| ha ·)

end

section

variable {M : Type*} {S T : Set M}

variable [Group M] {a b : M}

theorem inv_mem_centralizer (ha : a ∈ Set.centralizer S) : a⁻¹ ∈ Set.centralizer S := fun g hg ↦ by rw [mul_inv_eq_iff_eq_mul, mul_assoc, eq_inv_mul_iff_mul_eq, ha g hg]

end

section

variable {M : Type*} {S T : Set M}

variable {a c : M} [Mul M]

theorem left_comm (h : IsMulCentral a) (b c) : a * (b * c) = b * (a * c) := by
  simp only [(h.comm _).eq, h.right_assoc]

-- cf. `Commute.right_comm`

end

section

variable {M : Type*} {S T : Set M}

variable {a c : M} [Mul M]

theorem mid_assoc {z : M} (h : IsMulCentral z) (a c) : a * z * c = a * (z * c) := by
  rw [h.comm, ← h.right_assoc, ← h.comm, ← h.left_assoc, h.comm]

-- cf. `Commute.left_comm`

end

section

variable {M : Type*} {S T : Set M}

variable [Mul M]

theorem mul_mem_center {z₁ z₂ : M} (hz₁ : z₁ ∈ Set.center M) (hz₂ : z₂ ∈ Set.center M) :
    z₁ * z₂ ∈ Set.center M := by
  simp only [commute_iff_eq, Set.mem_center_iff, isMulCentral_iff] at *
  grind

end

section

variable {M : Type*} {S T : Set M}

variable [Semigroup M] {a b : M}

theorem mul_mem_centralizer (ha : a ∈ Set.centralizer S) (hb : b ∈ Set.centralizer S) :
    a * b ∈ Set.centralizer S := fun g hg ↦ by
  rw [mul_assoc, ← hb g hg, ← mul_assoc, ha g hg, mul_assoc]

end

section

variable {M : Type*} {S T : Set M}

variable [MulOneClass M]

theorem one_mem_center : (1 : M) ∈ Set.center M where
  comm _ := by rw [commute_iff_eq, one_mul, mul_one]
  left_assoc _ _ := by rw [one_mul, one_mul]
  right_assoc _ _ := by rw [mul_one, mul_one]

end

section

variable {M : Type*} {S T : Set M}

variable {a c : M} [Mul M]

theorem right_comm (h : IsMulCentral c) (a b) : a * b * c = a * c * b := by
  simp only [h.right_assoc, IsMulCentral.mid_assoc h, (h.comm _).eq]

end

section

variable {M : Type*} {S T : Set M}

variable [Monoid M]

theorem units_inv_mem_center {a : Mˣ} (ha : ↑a ∈ Set.center M) : ↑a⁻¹ ∈ Set.center M := by
  rw [Semigroup.mem_center_iff] at *
  exact (Commute.units_inv_right <| ha ·)

end
