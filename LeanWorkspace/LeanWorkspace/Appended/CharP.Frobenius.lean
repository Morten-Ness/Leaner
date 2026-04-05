import Mathlib

section

variable {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S]

variable (f : R →* S) (g : R →+* S) (p m n : ℕ) [ExpChar R p] [ExpChar S p] (x y : R)

theorem MonoidHom.map_iterate_frobenius (n : ℕ) :
    f ((frobenius R p)^[n] x) = (frobenius S p)^[n] (f x) := Function.Semiconj.iterate_right (f.map_frobenius p) n x

end

section

variable {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S]

variable (f : R →* S) (g : R →+* S) (p m n : ℕ) [ExpChar R p] [ExpChar S p] (x y : R)

theorem RingHom.iterateFrobenius_comm (n : ℕ) :
    g.comp (iterateFrobenius R p n) = (iterateFrobenius S p n).comp g := ext fun x ↦ map_iterateFrobenius g p x n

end

section

variable {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S]

variable (f : R →* S) (g : R →+* S) (p m n : ℕ) [ExpChar R p] [ExpChar S p] (x y : R)

theorem RingHom.map_iterateFrobenius (n : ℕ) :
    g (iterateFrobenius R p n x) = iterateFrobenius S p n (g x) := g.toMonoidHom.map_iterateFrobenius p x n

end

section

variable {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S]

variable (f : R →* S) (g : R →+* S) (p m n : ℕ) [ExpChar R p] [ExpChar S p] (x y : R)

theorem RingHom.map_iterate_frobenius (n : ℕ) :
    g ((frobenius R p)^[n] x) = (frobenius S p)^[n] (g x) := g.toMonoidHom.map_iterate_frobenius p x n

end

section

variable {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S]

variable (f : R →* S) (g : R →+* S) (p m n : ℕ) [ExpChar R p] [ExpChar S p] (x y : R)

theorem coe_iterateFrobenius_mul : iterateFrobenius R p (m * n) = (iterateFrobenius R p m)^[n] := funext (iterateFrobenius_mul_apply R p m n)

end

section

variable {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S]

variable (f : R →* S) (g : R →+* S) (p m n : ℕ) [ExpChar R p] [ExpChar S p] (x y : R)

theorem iterateFrobenius_add :
    iterateFrobenius R p (m + n) = (iterateFrobenius R p m).comp (iterateFrobenius R p n) := RingHom.ext (iterateFrobenius_add_apply R p m n)

end

section

variable {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S]

variable (f : R →* S) (g : R →+* S) (p m n : ℕ) [ExpChar R p] [ExpChar S p] (x y : R)

theorem iterateFrobenius_add_apply :
    iterateFrobenius R p (m + n) x = iterateFrobenius R p m (iterateFrobenius R p n x) := by
  simp_rw [iterateFrobenius_def, add_comm m n, pow_add, pow_mul]

end

section

variable {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S]

variable (f : R →* S) (g : R →+* S) (p m n : ℕ) [ExpChar R p] [ExpChar S p] (x y : R)

theorem iterateFrobenius_eq_pow : iterateFrobenius R p n = frobenius R p ^ n := by
  ext; simp [iterateFrobenius_def, iterate_frobenius]

end

section

variable {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S]

variable (f : R →* S) (g : R →+* S) (p m n : ℕ) [ExpChar R p] [ExpChar S p] (x y : R)

theorem iterateFrobenius_mul_apply :
    iterateFrobenius R p (m * n) x = (iterateFrobenius R p m)^[n] x := by
  simp_rw [coe_iterateFrobenius, Function.iterate_mul]

end

section

variable {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S]

variable (f : R →* S) (g : R →+* S) (p m n : ℕ) [ExpChar R p] [ExpChar S p] (x y : R)

theorem iterateFrobenius_one : iterateFrobenius R p 1 = frobenius R p := RingHom.ext (iterateFrobenius_one_apply R p)

end

section

variable {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S]

variable (f : R →* S) (g : R →+* S) (p m n : ℕ) [ExpChar R p] [ExpChar S p] (x y : R)

theorem iterateFrobenius_one_apply : iterateFrobenius R p 1 x = x ^ p := by
  rw [iterateFrobenius_def, pow_one]

end

section

variable {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S]

variable (f : R →* S) (g : R →+* S) (p m n : ℕ) [ExpChar R p] [ExpChar S p] (x y : R)

theorem iterateFrobenius_zero : iterateFrobenius R p 0 = RingHom.id R := RingHom.ext (iterateFrobenius_zero_apply R p)

end

section

variable {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S]

variable (f : R →* S) (g : R →+* S) (p m n : ℕ) [ExpChar R p] [ExpChar S p] (x y : R)

theorem iterateFrobenius_zero_apply : iterateFrobenius R p 0 x = x := by
  rw [iterateFrobenius_def, pow_zero, pow_one]

end
