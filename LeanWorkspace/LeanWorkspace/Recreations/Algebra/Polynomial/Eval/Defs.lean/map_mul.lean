import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

variable (f : R →+* S)

theorem map_mul : (p * q).map f = p.map f * q.map f := by
  rw [Polynomial.map, Polynomial.eval₂_mul_noncomm]
  exact fun k => (commute_X _).symm

-- `Polynomial.map` is a ring-hom unconditionally, and theoretically the definition could be replaced,
-- but this turns out not to be easy because `p.map f` does not resolve to `Polynomial.map`
-- if `Polynomial.map` is a `RingHom` instead of a plain function; the elaborator does not try to coerce
-- to a function before trying field (dot) notation (this may be technically infeasible);
-- the relevant code is (both lines): https://github.com/leanprover-community/
-- lean/blob/487ac5d7e9b34800502e1ddf3c7c806c01cf9d51/src/frontends/lean/elaborator.cpp#L1876-L1913

