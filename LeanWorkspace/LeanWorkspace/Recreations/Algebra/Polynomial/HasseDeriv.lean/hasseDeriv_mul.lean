import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] (k : ℕ) (f : R[X])

theorem hasseDeriv_mul (f g : R[X]) :
    Polynomial.hasseDeriv k (f * g) = ∑ ij ∈ antidiagonal k, Polynomial.hasseDeriv ij.1 f * Polynomial.hasseDeriv ij.2 g := by
  let D k := (@Polynomial.hasseDeriv R _ k).toAddMonoidHom
  let Φ := @AddMonoidHom.mul R[X] _
  change
    (compHom (D k)).comp Φ f g =
      ∑ ij ∈ antidiagonal k, ((compHom.comp ((compHom Φ) (D ij.1))).flip (D ij.2) f) g
  simp only [← finset_sum_apply]
  congr 2
  clear f g
  ext m r n s : 4
  simp only [Φ, D, finset_sum_apply, coe_mulLeft, coe_comp, flip_apply, Function.comp_apply,
             Polynomial.hasseDeriv_monomial, LinearMap.toAddMonoidHom_coe, compHom_apply_apply,
             coe_mul, monomial_mul_monomial]
  have aux :
    ∀ x : ℕ × ℕ,
      x ∈ antidiagonal k →
        monomial (m - x.1 + (n - x.2)) (↑(m.choose x.1) * r * (↑(n.choose x.2) * s)) =
          monomial (m + n - k) (↑(m.choose x.1) * ↑(n.choose x.2) * (r * s)) := by
    intro x hx
    rw [mem_antidiagonal] at hx
    subst hx
    by_cases! hm : m < x.1
    · simp only [Nat.choose_eq_zero_of_lt hm, Nat.cast_zero, zero_mul,
                 monomial_zero_right]
    by_cases! hn : n < x.2
    · simp only [Nat.choose_eq_zero_of_lt hn, Nat.cast_zero, zero_mul,
                 mul_zero, monomial_zero_right]
    rw [tsub_add_eq_add_tsub hm, ← add_tsub_assoc_of_le hn, ← tsub_add_eq_tsub_tsub,
      add_comm x.2 x.1, mul_assoc, ← mul_assoc r, ← (Nat.cast_commute _ r).eq, mul_assoc, mul_assoc]
  rw [Finset.sum_congr rfl aux]
  rw [← map_sum, ← Finset.sum_mul]
  congr
  rw_mod_cast [← Nat.add_choose_eq]

