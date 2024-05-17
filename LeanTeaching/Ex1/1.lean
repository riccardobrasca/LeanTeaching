import Mathlib.Tactic

/- ## Exercices autour du raisonnement logique - fichier 1/4 -/

/- ### Questions

Dans ces questions, on considère des objets `p`, `q`, `r` de type `Prop`.

1. Si vous devez prouver `p → q`, quelle tactique suggérez-vous d'utiliser ?

2. Si vous devez prouver `p ↔ q`, expliquez le rôle de la tactique `constructor`.

3. Si `h : p ∨ q`, expliquez ce que fait `rcases h with (hp | hq)`.

4. Si vous devez prouver `p ∨ q`, quelles tactiques pouvez-vous utiliser ?

5. Expliquer à quoi peut servir `Classical.em p : p ∨ ¬p` .
-/

/- ### Codage
Pour les exemples suivants, il n'est pas permis d'utiliser la tactique  `library_search`
(ni donc le résultat de mathlib qui démontre exactement le lemme demandé). -/

/-- Le `theorem` suivant est obligatoire. -/
theorem L1 (P Q R : Prop) (h1 : Q → P) (h2 : R → P) (h3 : Q ∨ R) : P := by
  sorry
  done

/- Choisissez *UN* entre les deux `theorem` suivants. -/
theorem L2 (P Q : Prop) (h : P ↔ ¬ Q) : (P → ¬ Q) ∧ (¬P → Q) := by
  sorry
  done

theorem L3 (P Q R : Prop) (h : P ∨ Q ∨ R → ¬(P ∧ Q ∧ R)) : (P ∨ Q) ∨ R → ¬((P ∧ Q) ∧ R) := by
  sorry
  done

/- Vous avez terminé le fichier 1.
*SAUVEGARDEZ IMMÉDIATEMENT VOTRE TRAVAIL SUR DISQUE DUR* et continuez avec le fichier 2.

Si vous en avez besoin, les instructions de l'examen sont à l'adresse https://github.com/riccardobrasca/LeanTeaching/blob/master/ex.md. -/
