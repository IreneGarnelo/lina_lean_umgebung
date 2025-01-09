-- Level name : "exact" Taktik

import data.nat.basic -- hide

/-
# Struktur in Lean
Die Struktur von Sätzen mit Beweis in Lean ist wiefolgt:

```
theorem Name (Voraussetzung 1) (Voraussetzung 2) : Folgerung :=
begin
...
end
```

Dabei kann der Name beliebig gewählt werden, sollte aber möglichst einen Einblick in
die Aussage des Satzes geben (in Lean heißt zum Beispiel der Satz zur Kommutativität
der Addition `add_comm`). Die Anzahl an Voraussetzungen kann variieren, es wurden nur
beispielhaft zwei vorgegeben. Zwischen `begin` und `end` stehen dann die Beweisschritte.

# "sorry" Keywort

Zu Beginn der Bearbeitung steht im Beweis immer sorry. Dies ist ein Keyword, was so viel
bedeutet wie: "Hier fehlt ein Teil des Beweises". Du kannst dieses Keyword verwenden, wenn 
ein Beweis überprüft werden soll, bei dem dir noch ein Teil fehlt. LEAN wird bestätigen, 
dass der Beweis stimmt, aber mit dem warning "uses sorry" darauf hinweisen, dass noch etwas 
zu tun ist. Lösche als Erstes das sorry, um mit dem Beweis zu starten.

# Beweisschritte
In Lean löst man Beweise, indem man Taktiken verwendet, die Beweisschritte
abbilden. Nach jedem Beweischritt muss man ein `,` einfügen, um dem Program mitzuteilen,
dass er den Schritt verarbeiten kann. In diesem Level werden wir die `exact` Taktik kennenlernen.
Diese kann verwendet werden, wenn eine der Aussagen `h`, die man in dem Beweiszustand sieht mit dem
Beweisziel übereinstimmt. Dann schreibt man `exact h,`. Das bedeutet in etwa so viel wie: "Die zu
Beweisende Aussage ist exakt die Aussage h."

Es gibt viele Taktiken in Lean, du kannst den Teil davon, den du für diese Lernumgebung
brauchst in der linken Spalte unter "Tactics" finden, wir werden diese aber Schritt für 
Schritt einführen.

# Erste Aufgabe
Wir möchten nun diese Taktik verwenden, um folgenden Satz zu zeigen: <br>
Sei $x \in \mathbb{N}$ und $x=2$. Dann ist $x=2$. <br>
Lies als erstes die Formulierung in Lean und versuche den Satz dort wiederzuerkennen.
Nutze dann die `exact` Taktik um den Beweis zu lösen.
-/

/- Theorem
Sei $x \in \mathbb{N}$ und $x=2$. Dann ist $x=2$.
-/
theorem beispiel_exact (x : nat) (h : x = 2) : x=2 :=
begin
exact h,
end