import Mathlib

variable {M : Type*} {S : Set M}

theorem add_mem_centralizer [Distrib M] (ha : a ∈ centralizer S) (hb : b ∈ centralizer S) :
    a + b ∈ centralizer S := fun c hc => by rw [add_mul, mul_add, ha c hc, hb c hc]

