import Mathlib

open scoped Polynomial

variable (p q : ℤ[X])

theorem irreducible_aux2 {k m m' n : ℕ} (hkm : k < m) (hmn : m < n) (hkm' : k < m') (hmn' : m' < n)
    (u v w : Units ℤ) (hp : p = Polynomial.trinomial k m n (u : ℤ) v w) (hq : q = Polynomial.trinomial k m' n (u : ℤ) v w)
    (h : p * p.mirror = q * q.mirror) : q = p ∨ q = p.mirror := by
  let f : ℤ[X] → ℤ[X] := fun p => ⟨Finsupp.filter (· ∈ Set.Ioo (k + n) (n + n)) p.toFinsupp⟩
  replace h := congr_arg f h
  replace h := (Polynomial.IsUnitTrinomial.irreducible_aux1 hkm hmn u v w hp).trans h
  replace h := h.trans (Polynomial.IsUnitTrinomial.irreducible_aux1 hkm' hmn' u v w hq).symm
  rw [(isUnit_C.mpr v.isUnit).mul_right_inj] at h
  rw [binomial_eq_binomial Polynomial.IsUnitTrinomial.ne_zero u Polynomial.IsUnitTrinomial.ne_zero w] at h
  simp only [add_left_inj, Units.val_inj] at h
  rcases h with (⟨rfl, -⟩ | ⟨rfl, rfl, h⟩ | ⟨-, hm, hm'⟩)
  · exact Or.inl (hq.trans hp.symm)
  · refine Or.inr ?_
    rw [← Polynomial.trinomial_mirror hkm' hmn' Polynomial.IsUnitTrinomial.ne_zero u Polynomial.IsUnitTrinomial.ne_zero u, eq_comm, mirror_eq_iff] at hp
    exact hq.trans hp
  · grind

