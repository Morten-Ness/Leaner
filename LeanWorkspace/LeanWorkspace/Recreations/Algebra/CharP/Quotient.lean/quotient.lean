import Mathlib

variable {R : Type*} [CommRing R]

theorem quotient (p : ℕ) [hp1 : Fact p.Prime] (hp2 : ↑p ∈ nonunits R) :
    CharP (R ⧸ (Ideal.span ({(p : R)} : Set R) : Ideal R)) p := have hp0 : (p : R ⧸ (Ideal.span {(p : R)} : Ideal R)) = 0 :=
    map_natCast (Ideal.Quotient.mk (Ideal.span {(p : R)} : Ideal R)) p ▸
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span <| Set.mem_singleton _)
  ringChar.of_eq <|
    Or.resolve_left ((Nat.dvd_prime hp1.1).1 <| ringChar.dvd hp0) fun h1 =>
      hp2 <|
        isUnit_iff_dvd_one.2 <|
          Ideal.mem_span_singleton.1 <|
            Ideal.Quotient.eq_zero_iff_mem.1 <|
              @Subsingleton.elim _ (@CharOne.subsingleton _ _ (ringChar.of_eq h1)) _ _

