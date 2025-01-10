-- Level name : Eindeutigkeit des Inversen Elements

import algebra.group.basic -- hide

/-
Nun werden wir auch die Eindeutigkeit des Inversen Elements zeigen.
Vergleiche die Formulierung des Satzes zum vorherigem, welche
Gemeinsamkeiten siehts du?

Du kannst wiefolgt umgehen: Schreibe mithilfe von `mul_one` und `one_mul`
(die Bedeutung davon kannst du unter Theorem Statements finden) das Beweisziel um,
sodass du `b*1=1*c` hast. Ersetze nun die beiden Einer durch das Produkt
von a mit jeweils den nach Voraussetzung gegebenen Inversen b und c. Wähle
dabei jeweils wie du jede Eins ersetzt so, dass du zum Schluss das Beweisziel durch
anwenden von Assoziativität (`mul_assoc`) lösen kannst.
-/

/- Theorem
Das Inverse eines Elements ist Eindeutig.
-/
theorem eind_inv {G : Type} [group G] (a b c : G)
  (hb : b * a = 1 ∧ a * b = 1) (hc : c * a = 1 ∧ a * c = 1) :
  b = c :=
begin
  rw ← mul_one b,
  rw ← one_mul c,
  conv {
    to_lhs, 
    rw ← hc.right,
  },
  rw ← hb.1,
  rw mul_assoc,




  
end
