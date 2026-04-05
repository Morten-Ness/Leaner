import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [CommSemiring R] {p : R[X]}

variable [NoZeroDivisors R] {p q : R[X]}

theorem Monic.irreducible_iff_natDegree' (hp : p.Monic) : Irreducible p ↔ p ≠ 1 ∧
    ∀ f g : R[X], f.Monic → g.Monic → f * g = p → g.natDegree ∉ Ioc 0 (p.natDegree / 2) := by
  simp_rw [hp.irreducible_iff_natDegree, mem_Ioc, Nat.le_div_iff_mul_le zero_lt_two, mul_two]
  apply and_congr_right'
  constructor <;> intro h f g hf hg he <;> subst he
  · rw [Polynomial.Monic.natDegree_mul hf hg, add_le_add_iff_right]
    exact fun ha => (h f g hf hg rfl).elim (ha.1.trans_le ha.2).ne' ha.1.ne'
  · simp_rw [Polynomial.Monic.natDegree_mul hf hg, pos_iff_ne_zero] at h
    contrapose! h
    obtain hl | hl := le_total f.natDegree g.natDegree
    · exact ⟨g, f, hg, hf, mul_comm g f, h.1, by gcongr⟩
    · exact ⟨f, g, hf, hg, rfl, h.2, by gcongr⟩

