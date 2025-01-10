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

/- Tactic : exact
## Anleitung
Wenn `h` eine Aussage ist, die exakt gleich zu dem Beweisziel
ist, dann löst `exact h` den Beweis.
## Beispiel
Bei folgendem Zustand:
```
x y : N
h : x + 1 = y
⊢ x + 1 = y
```
löst `exact h` den Beweis.
-/

/- Tactic : rw
## Anleitung
Wenn `h` eine Aussage des Typs `X = Y` ist, dann wird
`rw [h],` alle `X` in der zu beweisenden Aussage durch
`Y` austauschen.
Um alle `Y` durch `X` zu ersetzten verwendet man `rw [← h]`.
## Beispiel
Bei folgendem Zustand:
```
x : N
h : x + 0 = 0
⊢ succ (x + 0) = succ (x)
```
wird `rw [h],` das Ziel umändern zu `⊢ succ (x) = succ (x)`,
und damit den Beweis abschließen.
## Erweitert
1. Man kann einen konkreten Teil des Zustands konkretisieren,
um vorzugeben wo LEAN `rw` anwenden soll. Bei dem Zustand:
```
x y : N
h : x + 1 = y
⊢ x + 0 + 1 = y + 0
```
wird `rw [add_zero(x)],` den Zustand zu `x + 1 = y + 0` ändern und
`rw [add_zero(y)],` zu `x + 0 + 1 = y`
2. Man kann rw auch auf gegebene Aussagen anwenden statt auf
den Beweiszustand.Bei dem Zustand:
```
x : N
h : x + 0 = 3
⊢ x = 3 + 0
```
wird `rw [add_zero] at h,` den Beweiszustand nicht ändern, dafür aber
`h` umformen zu `h : x = 3`
-/

/- Tactic : repeat
## Anleitung
für einen Beweisschritt `step,`, führt `repeat {step,},` so oft den
Beweisschritt aus wie es möglich ist.
## Beispiel
Bei folgendem Zustand:
```
a : N, 
⊢ a + 0 + 0 + 0 = a
```
wird `repeat{rw [add_zero],},` dreimal den Befehl `rw [add_zero]` anwenden
und somit das Beweisziel zu `a=a` umformen und den Beweis schließen.
-/

/- Tactic : have
## Anleitung
Die Taktik have in LEAN erlaubt es, einen Zwischenschritt während eines Beweises 
zu definieren, welches bewiesen werden soll um im restlichem Beweis verwendet
zu werden.
## Beispiel
Bei folgendem Zustand:
```
a: ℕ
h: a + 2 = 4
⊢ a + 3 = 5
```
wird 
```
have ha : a = 2,
{...},
```
das Ziel ha einführen, welches in den Klammern bewiesen werden soll und dann
im Verlauf des Beweises verwendet werden darf.
-/

/- Tactic : conv
## Anleitung
Die Taktik `conv` wird verwendet, um gezielt Teile eines Beweisziels oder einer
Aussage umzuwandeln. Insbesondere wird sie im Zusammenhang mit `to_lhs` oder
`to_rhs` verwendet um jeweils Umformungen auf der linken oder rechten Seite
des Beweiszieles auszuführen.
## Beispiel
Bei folgendem Zustand:
```
x y : ℕ  
h : x + y = y + x  
⊢ x + y + 1 = 1 + x + y
```
kann `conv` genutzt werden, um nur die linke Seite des Ziels zu verändern:
```
conv { to_lhs, rw h, },
```
Das Ziel wird dadurch zu:
```
⊢ y + x + 1 = 1 + x + y
```
-/

/- Tactic : intro
## Anleitung
Die Taktik `intro` wird verwendet, um eine Annahme aus einem gegebenen
Implikationsziel oder einem quantifizierten Ziel (∀) zu übernehmen.
## Beispiel
Bei folgendem Zustand:
```
⊢ ∀ x : ℕ, x + 0 = x
```
kann `intro x,` genutzt werden, um `x` als eine Annahme einzuführen:
```
x : ℕ  
⊢ x + 0 = x 
``` 
## Erweitert
Mit intro h kann man der eingeführten Annahme einen bestimmten Namen (z. B. `h`) geben.
Mehrere Annahmen können durch `intros` gleichzeitig eingeführt werden.
-/

/- Tactic : refl
## Anleitung
Die Taktik `refl` wird verwendet, um ein Ziel zu lösen, bei dem die linke und 
rechte Seite eines Gleichheitszeichens trivialerweise bereits gleich sind.
## Beispiel
Bei folgendem Zustand:
```
⊢ 2+1 = 3  
```
löst `refl` den Beweis direkt.
-/

/- Tactic : specialize
## Anleitung
Die Taktik `specialize` wird verwendet, um eine allgemeine Aussage
mit einerm Quantor (∀) auf einen konkreten Fall anzuwenden.
## Beispiel
Bei folgendem Zustand:
```
h : ∀ x : ℕ, x + 0 = x  
⊢ 3 + 0 = 3  
```
kann `specialize h 3,` genutzt werden, um h auf den Wert 3 anzuwenden:
```
h : 3 + 0 = 3  
⊢ 3 + 0 = 3  
``` 
-/

/- Tactic : cases
## Anleitung
Für eine Aussage `h : h1 ∧ h2` teilt `cases h with f g,`
die Aussage auf, sodass man die Aussagen `f : h1` und `g : h2` erhält.
## Beispiel
Bei folgendem Zustand:
```
ab: ℕ
h: a + b = 8 ∧ b = 3
⊢ a = 5
```
führt `cases h with hab hb,` zu:
```
ab: ℕ
hab: a + b = 8
hb: b = 3
⊢ a = 5
```
.
-/

/- Tactic : by_cases
## Anleitung
`by_cases h : ha,` startet eine Fallunterscheidung. In einem Fall gilt `h : ha` und im
anderen gilt `h : ¬ha`. In beiden muss das ursprüngliche Beweisziel gezeigt werden.
## Beispiel
Wenn
man in LEAN `by_cases h: a>4,` verwendet, dann teilt LEAN den Beweiszustand in zwei
Teile. In beiden ist das Beweisziel das gleiche, in einem haben wir jedoch die
Aussage `h : a>4` und in dem anderen die Aussage `h : ¬ a>4`. Wie bei anderen Tactics
die den Beweis aufteilen kannst du auch hier Klammern verwenden und somit folgende
Struktur verwenden:
```
by_cases h: a>4,
{},
{},
```
-/

/- Tactic : apply
## Anleitung
Wenn die Voraussetzungen eines anderen Satz in dem Beweiszustand
gegeben sind und das Beweisziel das Ergebnis dieses Satzes ist, kann
mit `apply Satz Voraussetzungen,` das Ziel gelöst werden.
## Beispiel
Wenn zum Beispiel der Satz:
```
mul_gerade (a b : ℕ) 
(hger : ∃ c : ℕ, a=2*c) : ∃ d : ℕ, a*b = 2*d
```
bereits bewiesen wurde und der Beweiszustand:
```
c d : ℕ
hc: ∃ (e : ℕ), c = 2 * e
⊢ ∃ (f : ℕ), c * d = 2 * f
```
ist kann man `apply mul_gerade c d hc,` angewandt werden um den Beweis
zu lösen. Wichtig ist die Reihenfolge der Voraussetzungen.
-/

/- Axiom : add_zero (a : nat) :
a + 0 = a
-/

/- Axiom : add_assoc {G : Type} [group G] (a b c : G):
a + b + c = a + (b + c) 
-/

/- Axiom : add_comm {G : Type} [group G] (a b : G):
a + b = b + a 
-/

/- Axiom : mul_zero {F : Type} [field F] (a : F):
a * 0 = 0 
-/

/- Axiom : zero_mul {F : Type} [field F] (a : F):
0 * a = 0 
-/

/- Axiom : mul_one {G : Type} [group G] (a : G):
a * 1 = a 
-/

/- Axiom : one_mul {G : Type} [group G] (a : G):
1 * a = a 
-/

/- Axiom : mul_assoc {G : Type} [group G] (a b c : G):
a * b * c = a * (b * c) 
-/

/- Axiom : mul_comm {F : Type} [field F] (a b : F):
a * b = b * a 
-/

/- Axiom : mul_add {G : Type} [group G] (a b c : G):
a * (b + c) = a * b + a * c
-/

/- Axiom : pow_two {G : Type} [group G] (a : G):
a ^ 2 = a * a
-/

/- Axiom : mul_left_inv {G : Type} [group G] (a : G):
a⁻¹ * a = 1
-/

/- Axiom : mul_inv_rev {G : Type} [group G] (a b : G):
(a * b)⁻¹ = b⁻¹ * a⁻¹
-/

/- Axiom : inv_inv : {G : Type} [group G] (a : G):
a⁻¹⁻¹ = a
-/

/- Axiom: mul_inv_cancel {F : Type} [field F] {a : F}:
a ≠ 0 → a * a⁻¹ = 1
-/

/- Axiom: eq_inv_of_mul_eq_one {G : Type} [group G] {a b : G}:
a * b = 1 → a = b⁻¹
-/

/- Axiom: div_eq_mul_inv {F : Type} [field F] (a b : F):
a / b = a * b⁻¹
-/