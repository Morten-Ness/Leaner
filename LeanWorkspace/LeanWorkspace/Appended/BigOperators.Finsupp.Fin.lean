import Mathlib

section

variable {M N : Type*}

theorem finTwoArrowEquiv'_sum_eq {d : M × M} [AddCommMonoid M] :
    (((finTwoArrowEquiv' M).symm d).sum fun _ n ↦ n) = d.1 + d.2 := by
  apply (Finsupp.equivFunOnFinite_symm_sum _).trans
  simp

end

section

variable {M N : Type*}

theorem ofSupportFinite_fin_two_eq (n : Fin 2 →₀ ℕ) :
    ofSupportFinite ![n 0, n 1] (Set.toFinite _) = n := by
  rw [Finsupp.ext_iff, Fin.forall_fin_two]
  exact ⟨rfl, rfl⟩

end

section

variable {M N : Type*}

theorem sum_cons' [Zero M] [AddCommMonoid N] (n : ℕ) (σ : Fin n →₀ M) (i : M)
    (f : Fin (n + 1) → M → N) (h : ∀ x, f x 0 = 0) :
    (sum (Finsupp.cons i σ) f) = f 0 i + sum σ (Fin.tail f) := by
  rw [sum_fintype _ _ (fun _ => by apply h), sum_fintype _ _ (fun _ => by apply h)]
  simp_rw [Fin.sum_univ_succ, cons_zero, cons_succ]
  congr

end

section

variable {M N : Type*}

theorem sum_cons [AddCommMonoid M] (n : ℕ) (σ : Fin n →₀ M) (i : M) :
    (sum (cons i σ) fun _ e ↦ e) = i + sum σ (fun _ e ↦ e) := by
  rw [sum_fintype _ _ (fun _ => rfl), sum_fintype _ _ (fun _ => rfl)]
  exact Fin.sum_cons i σ

end
