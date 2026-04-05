import Mathlib

variable {l : Type ul} {m : Type um} {m₀ : Type um₀} {n : Type un} {n₀ : Type un₀} {o : Type uo}

variable {R : Type uR}

variable [Semiring R]

theorem lift_cRank_submatrix_le (A : Matrix m n R) (r : m₀ → m) (c : n₀ → n) :
    lift.{um} (A.submatrix r c).cRank ≤ lift.{um₀} A.cRank := by
  have h : ((A.submatrix r id).submatrix id c).cRank ≤ (A.submatrix r id).cRank :=
    Submodule.rank_mono <| span_mono <| by rintro _ ⟨x, rfl⟩; exact ⟨c x, rfl⟩
  refine (Cardinal.lift_monotone h).trans ?_
  let f : (m → R) →ₗ[R] (m₀ → R) := LinearMap.funLeft R R r
  have h_eq : Submodule.map f (span R (Set.range Aᵀ)) = span R (Set.range (A.submatrix r id)ᵀ) := by
    rw [LinearMap.map_span, ← image_univ, image_image, transpose_submatrix]
    aesop
  rw [Matrix.cRank, ← h_eq]
  have hwin := lift_rank_map_le f (span R (Set.range Aᵀ))
  simp_rw [← lift_umax] at hwin ⊢
  exact hwin

