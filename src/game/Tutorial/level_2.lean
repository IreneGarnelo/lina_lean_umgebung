-- Level name : "rw" Taktik

import data.nat.basic -- hide

/-
Wir werden nun eine weitere Taktik namens "rw" (Abkürzung für rewrite) kennenlernen. 
Mit dieser Taktik kann man Aussagen auf das Beweisziel anwenden.

Wenn h eine Aussage ist (z.B. `h : a = b`), dann bewirkt `rw h,`, dass LEAN die Aussage 
`h` in das Beweisziel einsetzt. In diesem Fall würde Lean in dem Beweisziel jedes `a` mit 
einem `b` ersetzten. Man kann angeben, an welcher Stelle des Beweiszieles die Aussage
angewandt werden soll, indem man `rw h x,` schreibt. Wenn nur eine Stelle möglich ist,
dann kann man das Argument weglassen.

Wir werden folgende Aussage zeigen: <br>
Sei $x \in \mathbb{N}$ und $x=2$. Dann ist $x \cdot 2=2 \cdot 2$. <br>
Dazu muss man die gegebene Aussage $x=2$ einfach in das Beweisziel einsetzen. Probiere
das mit dem `rw` Befehl aus und vergesse nicht das Komma am Ende der Zeile.
-/

/- Theorem
Sei $x \in \mathbb{N}$ und $x=2$. Dann ist $x \cdot 2=2 \cdot 2$.
-/
theorem beispiel_rw (x : nat) (h : x = 2) : x*2 = 2*2 :=
begin
rw h,
end
