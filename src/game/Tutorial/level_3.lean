-- Level name : "rw" von rechts nach links

import data.nat.basic -- hide

/-
Wir haben im vorherigem Level gesehen, dass für die Aussage `h: a = b` der Befehl 
`rw [h]`, in dem Beweisziel jedes `a` durch ein `b` ersetzt. Aber wie kann man jedes `b`
durch ein `a` ersetzen? Dazu verwendet man den Befehl `rw ← h,`. Der Pfeil steht sozusagen 
dafür, dass LEAN die Aussage `h` von rechts nach links lesen soll. Du kannst den Pfeil mit
`\ l` (backslash + klein L) schreiben.

Es ist nun wieder die gleiche Lean Aufgabe wie im vorherigem Level gegeben. Du könntest
diese genauso lösen wie zuvor, aber erkennst du auch einen weiteren Weg der `←` verwendet?
-/

/- Theorem
Sei $x \in \mathbb{N}$ und $x=2$. Dann ist $x \cdot 2=2 \cdot 2$.
-/
theorem beispiel_rw (x : nat) (h : x = 2) : x*2 = 2*2 :=
begin
rw ← h,



end

/- Hint : Brauchst du Hilfe, um den zweiten Weg zu finden?
Statt $x$ durch zwei zu ersetzen könnte man auch die zweier durch $x$ ersetzen.
-/