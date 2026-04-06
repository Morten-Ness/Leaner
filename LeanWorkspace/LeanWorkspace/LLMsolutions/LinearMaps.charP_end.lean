FAIL
import Mathlib

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

theorem charP_end {p : ℕ} [hchar : CharP R p]
    (htorsion : ∃ x : M, Ideal.torsionOf R M x = ⊥) : CharP (M →ₗ[R] M) p where
  cast_eq_zero_iff n := by
    constructor
    · intro hn
      rcases htorsion with ⟨x, hx⟩
      have hnx : n • x = 0 := by
        exact LinearMap.congr_fun hn x
      have hmem : (n : R) ∈ Ideal.torsionOf R M x := by
        rw [Ideal.mem_torsionOf_iff]
        simpa [nsmul_eq_mul] using hnx
      have hz : (n : R) = 0 := by
        simpa [hx] using hmem
      exact (CharP.cast_eq_zero_iff (R := R) p n).mp hz
    · intro hn
      ext x
      have hz : (n : R) = 0 := (CharP.cast_eq_zero_iff (R := R) p n).mpr hn
      change (n : End R M) x = 0
      simp [hz]
