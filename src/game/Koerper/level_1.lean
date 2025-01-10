-- Level name : Eindeutigkeit des inversen Elements

import algebra.field.basic-- hide

/-
Wir werden uns nun mit Körpern (auf englisch fields) auseinandersetzen.
Um in einem Satz $F$ als Körper zu definieren schreibt man zu Beginn der Voraussetzungen
`{F : Type} [field F]`.

Du kannst den Beweis mit `rintro ⟨hxy, hxz⟩,` starten. Diese Taktik ist ähnlich zu
`intro` funktioniert aber mit Beweiszielen die in ihrer Implikation ein und-Operator
haben.
-/

/- Hint : Brauchst du Hilfe?
Nach dem `rintro` Befehl brauchst du nur noch `rw` schritte mit den Aussagen im Beweiszustand,
`mul_one`, `mul_assoc`, `mul_comm` und `one_mul`.
-/

/- Theorem
Das Inverse in Körpern ist eindeutig.
-/
theorem eind_inv {F : Type} [field F] (x y z : F) (hx : x ≠ 0) :
  x * y = 1 ∧ x * z = 1 → y = z :=
begin
  rintro ⟨hxy, hxz⟩,
  rw ← mul_one y,
  rw ← hxz,
  rw ← mul_assoc,
  rw mul_comm y x,
  rw hxy,
  rw one_mul,




  
end
