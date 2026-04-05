import Mathlib

variable {R : Type*} [CommSemiring R]

theorem eval₂_homogenize_of_eq_one {S : Type*} [CommSemiring S] {p : R[X]} {n : ℕ}
    (hn : natDegree p ≤ n) (f : R →+* S) (g : Fin 2 → S) (hg : g 1 = 1) :
    MvPolynomial.eval₂ f g (p.homogenize n) = p.eval₂ f (g 0) := by
  apply Polynomial.induction_with_natDegree_le
    (fun p ↦ MvPolynomial.eval₂ f g (p.homogenize n) = p.eval₂ f (g 0)) (N := n)
  · simp
  · simp +contextual [hg]
  · simp +contextual
  · assumption

