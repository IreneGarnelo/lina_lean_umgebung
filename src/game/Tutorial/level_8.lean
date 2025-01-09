-- Level name : "rw" auf Aussagen im Beweiszustand anwenden

import data.nat.basic -- hide

/-
Wir möchten nun eine neue Eigenschaft der Taktik `rw` einführen. Man kann `rw` auch auf
gegebene Aussagen aus dem Beweiszustand anwenden statt auf das Beweisziel. Man gibt dazu
mit `at NameAussage` an, auf welche Aussage `rw` angewandt werden soll.

In dieser Aufgabe starten wir mit folgendem Beweiszustand:
```
xy: ℕ
h1: x = 2
h2: y = x + 1
⊢ y = 3
```
Um `h1`in `h2` einzusetzen können wir `rw h1 at h2,` schreiben. Das Beweisziel wird
dadurch nicht geändert, aber `h2` wird zu `h2 : y = 2 + 1`. Probiere es in der Aufgabe aus.
-/

/- Theorem
Seien $x$ und $y \in \mathbb{N}$ mit $x=2$ und $y=x+1$. Dann ist $y=3$.
-/
theorem rw_at (x y : nat)(h1: x=2)(h2 : y=x+1) : y=3 :=
begin
rw h1 at h2,
exact h2,
end