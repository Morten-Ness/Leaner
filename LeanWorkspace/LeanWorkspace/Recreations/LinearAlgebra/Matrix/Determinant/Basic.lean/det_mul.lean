import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_mul (M N : Matrix n n R) : Matrix.det (M * N) = Matrix.det M * Matrix.det N := calc
    Matrix.det (M * N) = ∑ p : n → n, ∑ σ : Perm n, ε σ * ∏ i, M (σ i) (p i) * N (p i) i := by
      simp only [Matrix.det_apply', mul_apply, prod_univ_sum, mul_sum, Fintype.piFinset_univ]
      rw [Finset.sum_comm]
    _ = ∑ p : n → n with Function.Bijective p, ∑ σ : Perm n, ε σ * ∏ i, M (σ i) (p i) * N (p i) i := by
      refine (sum_subset (filter_subset _ _) fun f _ hbij ↦ Matrix.det_mul_aux ?_).symm
      simpa only [mem_filter_univ] using hbij
    _ = ∑ τ : Perm n, ∑ σ : Perm n, ε σ * ∏ i, M (σ i) (τ i) * N (τ i) i :=
      sum_bij (fun p h ↦ Equiv.ofBijective p (mem_filter.1 h).2) (fun _ _ ↦ mem_univ _)
        (fun _ _ _ _ h ↦ by injection h)
        (fun b _ ↦ ⟨b, mem_filter.2 ⟨mem_univ _, b.bijective⟩, coe_fn_injective rfl⟩) fun _ _ ↦ rfl
    _ = ∑ σ : Perm n, ∑ τ : Perm n, (∏ i, N (σ i) i) * ε τ * ∏ j, M (τ j) (σ j) := by
      simp only [mul_comm, mul_left_comm, prod_mul_distrib, mul_assoc]
    _ = ∑ σ : Perm n, ∑ τ : Perm n, (∏ i, N (σ i) i) * (ε σ * ε τ) * ∏ i, M (τ i) i :=
      (sum_congr rfl fun σ _ =>
        Fintype.sum_equiv (Equiv.mulRight σ⁻¹) _ _ fun τ => by
          have : (∏ j, M (τ j) (σ j)) = ∏ j, M ((τ * σ⁻¹) j) j := by
            rw [← (σ⁻¹ : _ ≃ _).prod_comp]
            simp
          have h : ε σ * ε (τ * σ⁻¹) = ε τ :=
            calc
              ε σ * ε (τ * σ⁻¹) = ε (τ * σ⁻¹ * σ) := by
                rw [mul_comm, sign_mul (τ * σ⁻¹)]
                simp only [Int.cast_mul, Units.val_mul]
              _ = ε τ := by simp only [inv_mul_cancel_right]
          simp_rw [Equiv.coe_mulRight, h]
          simp only [this])
    _ = Matrix.det M * Matrix.det N := by
      simp only [Matrix.det_apply', Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

