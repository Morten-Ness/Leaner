import Mathlib

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable {h e f : L}

variable {m : M} {μ : R} {t : IsSl2Triple h e f}

variable (P : HasPrimitiveVectorWith t m μ)

theorem pow_toEnd_f_eq_zero_of_eq_nat [IsDomain R] [CharZero R] [IsNoetherian R M] [IsTorsionFree R M]
    {n : ℕ} (hn : μ = n) : (ψ (n + 1)) = 0 := by
  by_contra h
  have : t.HasPrimitiveVectorWith (ψ (n + 1)) (n - 2 * (n + 1) : R) :=
    { ne_zero := h
      lie_h := (P.lie_h_pow_toEnd_f _).trans (by simp [hn])
      lie_e := (P.lie_e_pow_succ_toEnd_f _).trans (by simp [hn]) }
  obtain ⟨m, hm⟩ := IsSl2Triple.HasPrimitiveVectorWith.exists_nat this
  have : (n : ℤ) < m + 2 * (n + 1) := by lia
  exact this.ne (Int.cast_injective (α := R) <| by simpa [sub_eq_iff_eq_add] using hm)

