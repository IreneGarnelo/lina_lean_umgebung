-- Level name : Zwei Voraussetzungen - Teil 2

import data.nat.basic -- hide

/-
Wir haben nun fast die gleiche Aufgabe wie zuvor. Der einzige Unterschied ist,
dass die beiden Voraussetzungen des Satzes mit einem und-Operator zu einer
Voraussetzung zusammengefasst wurden. In solchen Fällen muss man, wenn man
die Voraussetzung anwenden möchte, spezifizieren welchen Teil davon man meint.
Wenn man die Aussage, die links vom und-Operator ist verwenden möchte schreibt man
`rw h.left,` und ansonsten `rw h.right,`.
-/

/- Theorem
Seien $x$ und $y \in \mathbb{N}$ mit $x=2$ und $y=3$. Dann ist $x + 1= y$.
-/
theorem zwei_voraus_2 (x y : nat)(h: x=2 ∧ y=3) : x+1=y :=
begin
rw h.left,
rw h.right,



end