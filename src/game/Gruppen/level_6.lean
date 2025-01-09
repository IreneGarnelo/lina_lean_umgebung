-- Level name : Falls $y^{-1} \cdot x^{-1} \cdot y \cdot x = 1$, dann ist $G$ abelsch

import algebra.group.basic
import game.Gruppen.level_5 --hide

/- Zuletzt möchten wir für Gruppen zeigen, dass falls $y^{-1} \cdot x^{-1} \cdot y \cdot x = 1$ für
alle $x,y \in G$ gilt, die Gruppe abelsch ist. Gehe dazu wiefolgt vor:
Zeige zunächst, dass die Voraussetzungen des Lemmas in Level 5 erfüllt sind. Führe dazu
ein Zwischenziel ein (für diesen Teil kannst du `eq_inv_of_mul_eq_one` und `mul_inv_rev` verwenden).
Dann kannst du mit `apply inv_abelsch,` das Resultat aus Level 5 anwenden. Wie kannst du nun den Beweis 
schließen?
 -/

/- Hint : Brauchst du Hilfe, das Zwischenergebnis zu beweisen?
Du kannst folgende Beweisstuktur verwenden und die sorry durch Beweisschritte austauschen:
```
{intros x y,
specialize h x y,
rw mul_assoc at h,
have h2 : y⁻¹ * x⁻¹ = (y * x)⁻¹,
{ sorry, },
have h3 : (y * x)⁻¹ = x⁻¹ * y⁻¹,
{ sorry, },
sorry,},
```
-/

-- Theorem: Falls $y^{-1} \cdot x^{-1} \cdot y \cdot x$ für alle $x, y \in G$, dann ist $G$ abelsch.
theorem inv_inv_abelsch {G : Type} [group G]
  (h : ∀ x y : G, y⁻¹ * x⁻¹ * y * x = 1) :
  ∀ x y : G, x * y = y * x :=
begin
  have h1 : ∀ x y : G, x⁻¹ * y⁻¹ = y⁻¹ * x⁻¹,
  {intros x y,
  -- From the hypothesis, specialize h to x and y
  specialize h x y,
  -- Regroup the terms in the hypothesis using associativity
  rw mul_assoc at h, -- y⁻¹ * x⁻¹ * (y * x) = 1
  -- Use the hypothesis to deduce that y⁻¹ * x⁻¹ is the inverse of y * x
  have h2 : y⁻¹ * x⁻¹ = (y * x)⁻¹,
  { exact eq_inv_of_mul_eq_one h, },
  -- The inverse of y * x is also x⁻¹ * y⁻¹ by group properties
  have h3 : (y * x)⁻¹ = x⁻¹ * y⁻¹,
  { exact mul_inv_rev y x, },
  -- Combine the two equalities: y⁻¹ * x⁻¹ = x⁻¹ * y⁻¹
  rw h3 at h2,
  exact h2.symm,},
  apply inv_abelsch,
  exact h1,
end
