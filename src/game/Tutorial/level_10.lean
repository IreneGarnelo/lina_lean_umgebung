-- Level name : "rw" einschränken.

import data.int.basic -- hide

/-
In Level 2 haben wir gesehen, dass man mit `rw h x,` spezifizieren kann, wo
die Aussage `h` angewandt werden soll. In einigen Fällen ist dieses `x` aber
nicht eindeutig. In der folgende Aufgabe werden wir zeigen, dass für ganze
Zahlen $a,b$ und $c$ gilt, dass falls $a+b=1$ und $b+c=1$, dann $a+1=1+c$.
Dazu können wir die beiden Einser im Ziel mit den beiden Voraussetzungen 
substituieren. Wenn wir aber nun `rw ← h2,` oder auch `rw ← h2 1,` verwenden,
dann ersetzt Lean beide Einser. Um diese Umformung auf die linke Seite der
Gleichung einzuschränken könne wir `conv` verwenden. `conv` öffnet ein
neues Scope, in dem man die Seite der Gleichung festlegen kann und dann
Umformungen durchführen kann.

Probiere, diese Aufgabe mit
```
conv{
  to_lhs,
  rw ← h2,
},
```
zu starten. `lhs` steht für left hand side. Entsprechend gibt es für die
rechte Seite `rhs`.
-/

/- Theorem
Seien $a, b$ und $c \in \mathbb{Z}$, $a+b=1$ und $b+c=1$. Dann ist $a+1=1+c$.
-/
theorem rw_to_lhs (a b c : ℤ) (h1 : a + b = 1) (h2 : b + c = 1) : a + 1 = 1 + c :=
begin
  conv{
    to_lhs,
    rw ← h2,
  },
  rw ← h1,
  rw add_assoc,
end