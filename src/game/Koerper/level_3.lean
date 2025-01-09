-- Level name : Wenn das Produkt $0$ ist, dann ist einer der Faktoren $0$

import algebra.field.basic-- hide

/-
In diesem Beweis werden wir eine Fallunterscheidung durchführen. Das tut man in 
Lean mit `by cases`. Die Struktur dieser Taktik siehr wiefolgt aus:
```
by_cases hx : x = 0,
{sorry,},
{sorry,},
```
In diesem Beispiel wird zwischen dem Fall $x=0$ und dem Fall $x \neq 0$ unterschieden.
Eine weitere Besonderheit dieses Levels ist es, dass im Beweisziel ein oder-Operator
ist. In solchen fällen kann man in verschiedenen Scopes angeben ob man gerade zeigt, dass
der linke oder der rechte Fall gilt. In Kombination mit `by_cases` sieht das wiefolgt aus:
```
by_cases hx : x = 0,
{left,
sorry,},
{right,
sorry,},
```
-/

-- Theorem: Für $x, y \in F$ gilt: falls $x \cdot y = 0$ dann ist $x=0$ oder $y=0$.
theorem prod_null_faktor_null {F : Type} [field F] (x y : F) : x * y = 0 → x = 0 ∨ y = 0 :=
begin
  intro h,
  by_cases hx : x = 0,
  {left,
  exact hx,},
  {right,
  have hx_inv : x⁻¹ * x = 1 := by {
    rw mul_comm,
    rw mul_inv_cancel,
    exact hx,
  },
    have hinv_x : x⁻¹ * (x * y) = x⁻¹ * 0,
    { rw h },
    rw ← mul_assoc at hinv_x,
    rw hx_inv at hinv_x,
    rw one_mul at hinv_x,
    rw mul_zero at hinv_x,
    exact hinv_x,
    },
end
