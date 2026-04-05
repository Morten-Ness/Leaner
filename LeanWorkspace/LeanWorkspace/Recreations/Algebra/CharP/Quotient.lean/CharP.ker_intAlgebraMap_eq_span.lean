import Mathlib

theorem CharP.ker_intAlgebraMap_eq_span
    {R : Type*} [Ring R] (p : ℕ) [CharP R p] :
    RingHom.ker (algebraMap ℤ R) = Ideal.span {(p : ℤ)} := by
  ext a
  simp [CharP.intCast_eq_zero_iff R p, Ideal.mem_span_singleton]

