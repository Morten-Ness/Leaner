import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

variable (f : R →+* S) (x : S)

variable [Semiring T]

theorem eval₂_mul_noncomm (hf : ∀ k, Commute (f <| q.coeff k) x) :
    eval₂ f x (p * q) = eval₂ f x p * eval₂ f x q := by
  rcases p with ⟨p⟩; rcases q with ⟨q⟩
  simp only [coeff] at hf
  simp only [← ofFinsupp_mul, Polynomial.eval₂_ofFinsupp]
  exact liftNC_mul _ _ p q fun {k n} _hn => (hf k).pow_right n

