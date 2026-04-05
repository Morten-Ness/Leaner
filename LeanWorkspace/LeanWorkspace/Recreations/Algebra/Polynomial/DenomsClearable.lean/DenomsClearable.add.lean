import Mathlib

open scoped Polynomial

variable {R K : Type*} [Semiring R] [CommSemiring K] {i : R →+* K}

variable {a b : R} {bi : K}

theorem DenomsClearable.add {N : ℕ} {f g : R[X]} :
    DenomsClearable a b N f i → DenomsClearable a b N g i → DenomsClearable a b N (f + g) i := fun ⟨Df, bf, bfu, Hf⟩ ⟨Dg, bg, bgu, Hg⟩ =>
  ⟨Df + Dg, bf, bfu, by
    rw [map_add, Polynomial.map_add, eval_add, mul_add, Hf, Hg]
    congr
    refine @inv_unique K _ (i b) bg bf ?_ ?_ <;> rwa [mul_comm]⟩

