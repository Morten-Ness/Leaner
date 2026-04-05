import Mathlib

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

theorem adjugate_fin_three_of (a b c d e f g h i : α) :
    Matrix.adjugate !![a, b, c; d, e, f; g, h, i] =
      !![  e * i  - f * h, -(b * i) + c * h,   b * f  - c * e;
         -(d * i) + f * g,   a * i  - c * g, -(a * f) + c * d;
           d * h  - e * g, -(a * h) + b * g,   a * e  - b * d] := Matrix.adjugate_fin_three _

