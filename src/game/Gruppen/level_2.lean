-- Level name : Falls $x \cdot y = x \cdot z$, dann ist $y=z$

import algebra.group.basic -- hide

/-
Als nächstes werden wir uns einen längeren Beweis anschauen. Da dieser
aus vielen Schritten besteht ist er vorgegeben, damit du ihn zusammen mit
dem Lean Output nachvollziehen kannst. Der Beweis funktioniert wiefolgt:
```
intro h,
  have h_inv : x⁻¹ * (x * y) = x⁻¹ * (x * z),
  { rw h, },
  rw [←mul_assoc, ←mul_assoc] at h_inv,
  rw mul_left_inv x at h_inv,
  repeat{ rw one_mul at h_inv, },
  exact h_inv,
```
Kannst du in Worten beschreiben was in jedem Schritt passiert? In dem Beweis kommt
die neue Taktik `repeat` vor. Kannst du aus dem Kontext erahnen was sie tut?
-/

/- Theorem
Die Gruppenverknüpfung ist eindeutig.
-/
theorem eind_mul {G : Type} [group G] (x y z : G) :
  x * y = x * z → y = z :=
begin
  intro h,
  have h_inv : x⁻¹ * (x * y) = x⁻¹ * (x * z),
  { rw h, },
  rw [←mul_assoc, ←mul_assoc] at h_inv,
  rw mul_left_inv x at h_inv,
  repeat{ rw one_mul at h_inv, },
  exact h_inv,
end
