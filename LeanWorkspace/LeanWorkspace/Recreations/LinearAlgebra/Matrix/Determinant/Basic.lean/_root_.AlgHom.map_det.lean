import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

variable {S : Type w} [CommRing S]

theorem _root_.AlgHom.map_det [Algebra R S] {T : Type z} [CommRing T] [Algebra R T] (f : S →ₐ[R] T)
    (M : Matrix n n S) : f M.det = Matrix.det (f.mapMatrix M) := f.toRingHom.map_det _

