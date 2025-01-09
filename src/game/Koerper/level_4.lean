-- Level name : Falls $x^2=0$ dann $x=0$

import algebra.field.basic-- hide
import algebra.group_power.basic --hide
import game.Koerper.level_3 --hide

/- 
Aus der vorherigen Aufgabe kann man folgern, dass falls $x^2=0$ dann $x=0$. Du kannst
dazu konkret den Satz, der in Level 3 bewiesen wurde verwenden. Da es in dem Satz
Fälle gibt musst du ihn wiefolgt anwenden: `cases prod_null_faktor_null x x h with hx hx,`
Verwende dazu `pow_two` und das Quadrat in eine Multiplikation umzuwandeln.
-/

-- Theorem: Für $x \in F$ gilt: falls $x^2 = 0$ dann ist $x=0$.
theorem quad_null_x_0 {F : Type} [field F] (x : F) : x^2 = 0 → x = 0 :=
begin
  intro h,
  rw pow_two x at h,
  cases prod_null_faktor_null x x h with hx hx,
  {exact hx,},
  {exact hx,},
end
