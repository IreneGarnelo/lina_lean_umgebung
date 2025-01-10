-- Level name : "intro" Taktik

import data.nat.basic -- hide


/-
Falls die Aussage, die zu zeigen ist eine Implikation enthält, wie das untere
Beispiel, dann würde man bei einem Beweis auf Papier schreiben "Seien $x$
und $y$ sodass ..." um konkrete Instanzen zu haben mit denen man rechnen kann.
In Lean tut man das mit `intro h,`.

Wenn man in der unteren Aufgabe `intro h,` anwendet, dann wird `h: x = 2 * y`
zu einer im Beweiszustand gegebenen Aussage und das Beweisziel ändert sich zur
Folgerung aus der Implikation, also `2*x = 4*y`.

Du kannst nun mit `rw` zusammen mit `h` und `mul_assoc` das Beweisziel zu
`2 * 2 * y = 4 * y` umformen. Ein Ziel dieser Art, auf den auf beiden Seiten
bis auf simple arithmetische Operationen das gleiche steht kannst du mit
`refl,` lösen.
-/

/- Theorem
Seien $x$ und $y \in \mathbb{N}$, dann folgt aus $x=2 /cdot y$, dass $2 /cdot x = 4 /cdot y$.
-/
example (x y : nat) : x = 2*y → 2*x = 4*y :=
begin
  intro h,
  rw h,
  rw ← mul_assoc,
  refl,


  
end