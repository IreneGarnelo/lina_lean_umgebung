-- Level name : Zwei Voraussetzungen - Teil 1

import data.nat.basic -- hide

/-
In der folgenden Aufgabe gibt es zwei Voraussetzungen. Benutze beide
zusammen mit `rw` um die Aufgabe zu lösen.
-/

/- Theorem
Seien $x$ und $y \in \mathbb{N}$ mit $x=2$ und $y=3$. Dann ist $x + 1= y$.
-/
theorem zwei_voraus_1 (x y : nat)(h1: x=2)(h2 : y=3) : x+1=y :=
begin
rw h1,
rw h2,
end