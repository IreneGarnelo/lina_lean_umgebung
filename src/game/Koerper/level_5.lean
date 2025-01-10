-- Level name : Kürzen von Brüchen

import algebra.field.basic-- hide

/- Zuletz zeigen wir, dass man Brüche kürzen kann. In diesem Beweis reicht es, mit `rw`
zu arbeiten. Suche dir dazu aus der linken Spalte die richtigen Sätze aus.
-/

-- Theorem: Für $x, y \in F$ mit $y \neq 0$ gilt: $\frac{x \cdot y}{y} = x$.
theorem kuerzen_brueche {F : Type} [field F] (x y : F) (hy : y ≠ 0) : x * y / y = x :=
begin
  rw div_eq_mul_inv,
  rw mul_assoc,
  rw mul_inv_cancel hy,
  rw mul_one,





  
end
