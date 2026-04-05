import Mathlib

open scoped Nat

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R]

theorem eval_multiset_prod_X_sub_C_derivative [DecidableEq R]
    {S : Multiset R} {r : R} (hr : r ∈ S) :
    eval r (Polynomial.derivative (Multiset.map (fun a => Polynomial.X - Polynomial.C a) S).prod) =
      (Multiset.map (fun a => r - a) (S.erase r)).prod := by
  nth_rw 1 [← Multiset.cons_erase hr]
  have := (evalRingHom r).map_multiset_prod (Multiset.map (fun a => Polynomial.X - Polynomial.C a) (S.erase r))
  simpa using this

