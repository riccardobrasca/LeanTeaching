import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Data.Nat.Parity
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/- **Démontrer avec un ordinateur**
Riccardo Brasca, Antoine Chambert-Loir
Séance 5 : Fonctions
(Mathematics in Lean, chapitre 4)-/

/- # Fonctions
On continue la discussion des ensembles en étudiant les fonctions et on revisite les notions classiques, images et images réciproques, fonctions injectives, surjectives, bijectives… -/

section

variable {α β : Type*} (f : α → β) (s t : Set α) (u v : Set β)
open Function Set

/- ## Image réciproque
Si `f : α → β` est une fonction et `u : set β`, alors `f ⁻¹' u` est de type `Set α`,
ses éléments sont les `x : α` tels que `f x ∈ s` -/

-- Comportement de l'image réciproque par intersection
example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl
  done

-- À vous
example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  sorry
  done

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  sorry
  done

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  sorry
  done

/- ## Image
Si `f : α → β` est une fonction et `s : Set α`, alors `f '' s` est de type `Set β`,
ses éléments sont les `y : β` tels qu'il existe `x ∈ s` vérifiant `y = f x`. -/

-- Comportement de l'image par réunion
example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y
  constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x
    · right
      use x
  · rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
    · use x
      constructor
      · left
        exact xs
      · rfl
    · use x
      constructor
      · right
        exact xt
      · rfl
  done

-- À vous
example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  sorry
  done

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  sorry
  done

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  sorry
  done

/- Notez qu'on a d'abord traité l'image réciproque,
avant l'image, et que les preuves sont un peu plus simples.Pouvez-vous expliquer en quoi ? -/

-- ## Relations entre image et image réciproque
example : s ⊆ f ⁻¹' (f '' s) := by
  intros x xs
  show f x ∈ f '' s
  use x
  done

-- À vous !
example : f '' (f⁻¹' u) ⊆ u := by
  sorry
  done

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  sorry
  done

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  sorry
  done

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∪ u := by
  sorry
  done

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  sorry
  done

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  sorry
  done

-- ## Injectivité, surjectivité, bijectivité
/- Les prédicats `injective`, `surjective`, `bijective` disent respectivement qu'une fonction est injective, surjective, bijective… -/
#print Injective
#print Surjective
#print Bijective

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  sorry
  done

example (h : Surjective f) : u ⊆ f '' (f⁻¹' u) := by
  sorry
  done

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  sorry
  done

-- ## Unions, intersections et images, images réciproques

variables {I : Type*} (A : I → Set α) (B : I → Set β)

/- Utilisez `ext` et `intro`, avant d'appeler `simp `.-/
example : f '' (⋃ i, A i) = ⋃ i, f '' A i := by
  ext y
  simp
  constructor
  · intro ⟨x, ⟨i, xAi⟩, fxeq⟩
    use i
    use x
  · intro ⟨i, x, xAi, fxeq⟩
    exact ⟨x, ⟨i, xAi⟩, fxeq⟩
  done

example : f '' (⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  intro y
  simp
  intros x h fxeq i
  use x
  constructor
  · exact h i
  · exact fxeq
  done

/- Dans cet exemple, on a besoin de `i : I` pour
garantir que `I` n'est pas vide. Est-ce que vous voyez pourquoi ? -/
example (i : I) (injf : Injective f) :
  (⋂ i, f '' A i) ⊆ f '' (⋂ i, A i) := by
  intro y
  simp
  intro h
  rcases h i with ⟨x, _xAi_, fxeq⟩
  use x
  constructor
  · intro i'
    rcases h i' with ⟨x', x'Ai, fx'eq⟩
    have : f x = f x' := by
      rw [fxeq, fx'eq]
    have : x = x' := by
      exact injf this
    rw [this]
    exact x'Ai
  · exact fxeq
  done

example : f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' (B i) := by
  ext x
  simp

example : f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i) := by
  ext x
  simp

end

-- # Des théorèmes de théorie des ensembles

-- ## Inverses à droite, à gauche

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) := Classical.choose_spec h

noncomputable section
open Classical

/- Étant donnée une fonction `f : α → β`,
on construit une fonction `inverse f : β → α` comme suit:
si `y : β`, et s'il existe `x : α` tel que `f x = y`, alors l'image de `y` est un de ces éléments,
donné par le choix `Classical.choose` ; sinon, on prend un élément par défaut de `α`
— donné par l'instance `Inhabited α` -/

def inverse (f : α → β) : β → α :=
fun y : β ↦ if h : ∃ x, f x = y then Classical.choose h else default

/- Si `y` a un antécédent, alors `f (inverse f y) = y` -/
theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) :
  f (inverse f y) = y := by
  rw [inverse]
  rw [dif_pos h]
  exact Classical.choose_spec h

variable  (f : α → β)
open Function

/- Prouvez que si `f` est injective, alors `inverse f` est inverse à gauche de `f` : (inverse f) ∘ f = id -/
example : Injective f ↔ LeftInverse (inverse f) f  := by
  sorry
  done

/- Prouvez que si `f` est surjective, alors `inverse f` est inverse à droite de `f` : f ∘ (inverse f) = id -/
example : Surjective f ↔ RightInverse (inverse f) f := by
  sorry
  done

end


/- ## Le théorème de Cantor
Le théorème de Cantor affirme que pour tout type `α`,
il n'existe pas de surjection `α → Set α`. La méthode utilisée par Georg Cantor à cette occasion
porte le nom d'*argument diagonal* et est reprise dans de nombreuses autres démonstrations.
Elle est proche de celle mise en œuvre par Russell pour démontrer son fameux paradoxe en théorie
des ensembles.

Voir Wikipedia pour une explication de la preuve
https://en.wikipedia.org/wiki/Cantor%27s_theorem

Je vous recommande aussi la lecture de la bande dessinée *Logicomix. An epic search for truth*,
qui raconte ces divers épisodes de l'histoire des mathématiques du début du 20e siècle.
L'un de ses auteurs est un informaticien très réputé, spécialiste d'algorithmique et de calculabilité.

-/
section Cantor

variable {α : Type*}
open Function

-- Vous allez devoir compléter la preuve
theorem Cantor : ∀ f : α → Set α, ¬ Surjective f := by
-- On suppose donnée une fonction `f : α → Set α` qui est surjective, et on veut prouver `False`.
  intros f surjf
-- On définit `S : Set α` comme l'ensemble des `i` tels que `i ∉ f i` et on va prouver
--`False` en contredisant l'hypothèse que `S` a un antécédent par `f`.
  let S := { i | i ∉ f i}
  rcases surjf S with ⟨j, h⟩
-- À ce stade, `j : α` est un antécédent de `S` par `f`
-- La preuve passe par trois intermédiaires
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by
      rwa [h] at h'
    contradiction

  have h₂ : j ∈ S := by
    sorry

  have h₃ : j ∉ S := by
    sorry
-- Lean finit par trouver une contradiction à partir de h₂ et h₃
  contradiction
  done

end Cantor

open Set
open Function

variables {α β : Type*} [Nonempty β]

noncomputable section
open Classical

section Schroder_Bernstein
/- ## Le théorème de Schröder-Bernstein

On démontre ici le théorème de Schröder-Bernstein :
Si `α` et `β` sont des types, et si `f : α → β ` et `g : β → α` sont des fonctions injectives,
alors il existe une fonction bijective `h : α → β`.
C'est un résultat très important de la théorie des ensemble s du début du 20e siècle, lorsqu'il
s'agissait de définir la notion de cardinal. Intuitivement, l'existence de `f` injective indique
que le cardinal de `α` est inférieur ou égal à celui de `β`, tandis que l'existence de `g`
injective indique que le cardinal de `β` est inférieur ou égal à celui de `α`.
La conclusion du théorème, qu'il existe `h : α → β` qui est bijective affirme que le cardinal de
`α` est égal à celui de `β`.

La preuve ci-dessous contient quelques `sorry`; essayez de les remplir !

Vous pouvez aller visiter Wikipedia pour lire une description de la preuve.

https://en.wikipedia.org/wiki/Schr%C3%B6der%E2%80%93Bernstein_theorem

-/

variable (f : α → β) (g : β → α)


def sb_aux : ℕ → Set α
| 0       => univ \ (g '' univ)
| (n + 1) => g '' (f '' sb_aux n)

def sb_set := ⋃ n, sb_aux f g n

/- Ici est définie la fonction qui conviendra dans le théorème -/
def sb_fun (x : α) : β := if x ∈ sb_set f g then f x else invFun g x

theorem sb_right_inv {x : α} (hx : x ∉ sb_set f g) :
    g (invFun g x) = x := by
  have : x ∈ g '' univ := by
    contrapose! hx
    rw [sb_set, mem_iUnion]
    use 0
    rw [sb_aux, mem_diff]
    sorry
  have : ∃ y, g y = x := by
    sorry
  sorry
  done

theorem sb_injective (hf: Injective f) :
    Injective (sb_fun f g) := by
  set A := sb_set f g with A_def
  set h := sb_fun f g with h_def
  intro x₁ x₂ hxeq
  simp only [h_def, sb_fun, ←A_def] at hxeq
  by_cases xA : x₁ ∈ A ∨ x₂ ∈ A
  · rcases xA with (xA | xA)
    · have x₂A : x₂ ∈ A := by
        apply not_imp_self.mp
        intro x₂nA
        rw [if_pos xA, if_neg x₂nA] at hxeq
        rw [A_def, sb_set, mem_iUnion] at xA
        have x₂eq : x₂ = g (f x₁) := by
          rw [← sb_right_inv f g x₂nA, hxeq]
        rcases xA with ⟨n, hn⟩
        rw [A_def, sb_set, mem_iUnion]
        use n + 1
        simp [sb_aux]
        exact ⟨x₁, hn, x₂eq.symm⟩
      simp [xA, x₂A] at hxeq
      exact hf hxeq
    · have x₁A : x₁ ∈ A := by
        apply not_imp_self.mp
        intro x₁nA
        rw [if_pos xA, if_neg x₁nA] at hxeq
        rw [A_def, sb_set, mem_iUnion] at xA
        have x₁eq : x₁ = g (f x₂) := by
          rw [← sb_right_inv f g x₁nA, hxeq]
        rcases xA with ⟨n, hn⟩
        rw [A_def, sb_set, mem_iUnion]
        use n + 1
        simp [sb_aux]
        exact ⟨x₂, hn, x₁eq.symm⟩
      simp [xA, x₁A] at hxeq
      exact hf hxeq
  · push_neg at xA
    simp [xA] at hxeq
    rw [← sb_right_inv f g xA.1, ← sb_right_inv f g xA.2, hxeq]

  done

theorem sb_surjective (hg : Injective g) :
    Surjective (sb_fun f g) := by
  set A := sb_set f g with A_def
  set h := sb_fun f g with h_def
  intro y
  by_cases gyA : g y ∈ A
  · rw [A_def, sb_set, mem_iUnion] at gyA
    rcases gyA with ⟨n, hn⟩
    cases n with
    | zero =>
      simp [sb_aux] at hn
    | succ n =>
      simp [sb_aux] at hn
      rcases hn with ⟨x, xmem, hx⟩
      use x
      have : x ∈ A := by
        rw [A_def, sb_set, mem_iUnion]
        exact ⟨n, xmem⟩
      simp only [h_def, sb_fun, if_pos this]
      exact hg hx
  · use g y
    simp [sb_fun, gyA]
    apply hg
    exact apply_invFun_apply
  done

end Schroder_Bernstein

/- La preuve finale est courte, on utilise que `bijective h` se récrit en `injective h ∧ surjective h`. -/
theorem schroeder_bernstein {f : α → β} {g : β → α}
    (hf: Injective f) (hg : Injective g) :
  ∃ h : α → β, Bijective h :=
⟨sb_fun f g, sb_injective f g hf, sb_surjective f g hg⟩
