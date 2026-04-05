import Mathlib

section

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [Semiring M] [Module ℚ≥0 M]

theorem expect_mul_expect [IsScalarTower ℚ≥0 M M] [SMulCommClass ℚ≥0 M M] (s : Finset ι)
    (t : Finset κ) (f : ι → M) (g : κ → M) :
    (𝔼 i ∈ s, f i) * 𝔼 j ∈ t, g j = 𝔼 i ∈ s, 𝔼 j ∈ t, f i * g j := by
  simp_rw [Finset.expect_mul, Finset.mul_expect]

end

section

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [AddCommMonoid M] [Module ℚ≥0 M] [AddCommMonoid N] [Module ℚ≥0 N] {s t : Finset ι}
  {f g : ι → M} {p q : ι → Prop} [DecidablePred p] [DecidablePred q]

theorem exists_ne_zero_of_expect_ne_zero (h : 𝔼 i ∈ s, f i ≠ 0) : ∃ i ∈ s, f i ≠ 0 := by
  contrapose! h; exact Finset.expect_eq_zero h

end

section

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [AddCommMonoid M] [Module ℚ≥0 M] [AddCommMonoid N] [Module ℚ≥0 N] {s t : Finset ι}
  {f g : ι → M} {p q : ι → Prop} [DecidablePred p] [DecidablePred q]

theorem expect_add_expect_comm (f₁ f₂ g₁ g₂ : ι → M) :
    𝔼 i ∈ s, (f₁ i + f₂ i) + 𝔼 i ∈ s, (g₁ i + g₂ i) =
      𝔼 i ∈ s, (f₁ i + g₁ i) + 𝔼 i ∈ s, (f₂ i + g₂ i) := by
  simp_rw [Finset.expect_add_distrib, add_add_add_comm]

end

section

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [Fintype ι] [Fintype κ]

variable [AddCommMonoid M] [Module ℚ≥0 M]

theorem expect_bijective (e : ι → κ) (he : Function.Bijective e) (f : ι → M) (g : κ → M)
    (h : ∀ i, f i = g (e i)) : 𝔼 i, f i = 𝔼 i, g i := Finset.expect_nbij e (fun _ _ ↦ Finset.mem_univ _) (fun i _ ↦ h i) he.injective.injOn <| by
    simpa using he.surjective

end

section

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [Semifield M] [CharZero M]

theorem expect_boole_mul' [Fintype ι] [Nonempty ι] [DecidableEq ι] (f : ι → M) (i : ι) :
    𝔼 j, ite (j = i) (Fintype.card ι : M) 0 * f j = f i := by
  simp_rw [@eq_comm _ _ i, Finset.expect_boole_mul]

end

section

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [Semifield M] [CharZero M]

theorem expect_div (s : Finset ι) (f : ι → M) (a : M) : (𝔼 i ∈ s, f i) / a = 𝔼 i ∈ s, f i / a := by
  simp_rw [div_eq_mul_inv, Finset.expect_mul]

end

section

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [AddCommMonoid M] [Module ℚ≥0 M] [AddCommMonoid N] [Module ℚ≥0 N] {s t : Finset ι}
  {f g : ι → M} {p q : ι → Prop} [DecidablePred p] [DecidablePred q]

theorem expect_eq_zero (h : ∀ i ∈ s, f i = 0) : 𝔼 i ∈ s, f i = 0 := (Finset.expect_congr rfl h).trans s.expect_const_zero

end
