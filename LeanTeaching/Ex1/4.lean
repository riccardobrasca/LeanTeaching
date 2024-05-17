import Mathlib.Data.Set.Image

open Function

/-  ## Exercices sur les ensembles - fichier 4/4

 ### Questions

Soient `f : α → β`, où `α β : Type`, `s : Set α` et `t : Set β`.

1. Donner la définition mathématique de `f '' s`.

2. Donner la définition mathématique de `f ⁻¹' t`.

 -/


/- ### Codage
Pour les exemples suivants, il n'est pas permis d'utiliser la tactique  `exact?`
(ni donc le résultat de mathlib qui démontre exactement le lemme demandé).-/

variable {α β : Type} (f : α → β) (t : Set α)

/-- Le `theorem` suivant est obligatoire. -/
theorem S1 : t ⊆ f ⁻¹' (f '' t) := by
  sorry
  done

/- Choisissez *UN* entre les deux `theorem` suivants. -/
theorem S2 (hf : Injective f) : t = f ⁻¹' (f '' t) := by
  sorry
  done

theorem S3 (f : α → β) (s : Set β) (t : Set α) :
  t ∪ f ⁻¹' s ⊆ f ⁻¹' (f '' t ∪ s) := by
  sorry
  done

/- Vous avez terminé le fichier 4 et donc l'examen.
*SAUVEGARDEZ IMMÉDIATEMENT VOTRE TRAVAIL SUR DISQUE DUR*.

Vous devez maintenant déposer les quatre fichiers sur Moodle, ne l'oubliez pas !

Si vous en avez besoin, les instructions de l'examen sont à l'adresse https://github.com/riccardobrasca/LeanTeaching/blob/master/ex.md. -/
