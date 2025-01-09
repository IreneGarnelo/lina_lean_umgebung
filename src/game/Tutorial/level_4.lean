-- Level name : "rw" und gegebene Sätze

import data.nat.basic -- hide

/-
Man kann die Taktik `rw` auch in Verknüpfüng mit bekannten Sätze verwenden. In
Lean ist viel der Mathematik mit der wir an der Uni arbeiten implementiert und kann
in Beweisen verwendet werden. In der linken Spalte findest du unter "Theorem statements"
einiger solche Sätze, die für diese Lernumgebung nützlich sein könnten.

Einer dieser Sätze ist `mul_one` und sagt aus, dass für eine natürliche Zahl
$x$ gilt, dass `x*1=` ist. Wenn man also in einem Beweiszustand `x*1` hat, kann
man das mit `rw mul_one,` vereinfachen. Probiere es in dieser Aufgabe aus.
-/

/- Theorem
Sei $x \in \mathbb{N}$. Dann ist $x \cdot 1=x$.
-/
theorem rw_mul_one (x : nat) : x*1=x :=
begin
rw mul_one,
end