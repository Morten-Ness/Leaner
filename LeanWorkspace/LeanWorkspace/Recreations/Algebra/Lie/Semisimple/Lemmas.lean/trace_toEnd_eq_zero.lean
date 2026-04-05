import Mathlib

variable (k L M : Type*) [Field k] [CharZero k]
  [LieRing L] [LieAlgebra k L] [Module.Finite k L]
  [AddCommGroup M] [Module k M] [LieRingModule L M] [LieModule k L M] [Module.Finite k M]
  [IsIrreducible k L M] [IsFaithful k L M] [IsTriangularizable k L M]

variable {R : Type*} [CommRing R] [LieAlgebra R L] [Module R M] [LieModule R L M]

theorem trace_toEnd_eq_zero {s : Set L} (hs : ∀ x ∈ s, LinearMap.trace R _ (toEnd R _ M x) = 0)
    {x : L} (hx : x ∈ LieSubalgebra.lieSpan R L s) :
    trace R _ (toEnd R _ M x) = 0 := by
  induction hx using LieSubalgebra.lieSpan_induction with
  | mem u hu => simpa using hs u hu
  | zero => simp
  | add u v _ _ hu hv => simp [hu, hv]
  | smul t u _ hu => simp [hu]
  | lie u v _ _ _ _ => simp

