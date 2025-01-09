-- Level name : Zwei Voraussetzungen - Teil 3

import data.nat.basic -- hide

/-
Wir haben die exakte Aufgabe wie zuvor, möchten aber nun sehen, dass wir den
beiden Aussagen, die mit einem und-Operator" verbunden wurden, Namen geben können
um diese wieder einzeln verweden zu können. Das lohnt sich insbesondere wenn man
in einem Beweis die Teilaussagen öfter braucht. Dazu verwendet man `have` wiefolgt: <br>
`have h1 := h.left`. Statt `h1` kann man einen beliebigen Namen wählen.

Führe in der unteren Aufgabe die Aussagen `h1` und `h2` ein und benutze sie um den Beweis
mit `rw` zu lösen.
-/

/- Theorem
Seien $x$ und $y \in \mathbb{N}$ mit $x=2$ und $y=3$. Dann ist $x + 1= y$.
-/
theorem zwei_voraus_2 (x y : nat)(h: x=2 ∧ y=3) : x+1=y :=
begin
have h1 := h.left,
have h2 := h.right,
rw h1,
rw h2,
end