%title: Metody Formalne, wykład 5 
%author: Tomasz Brengos
%date: 2024-03-25


-> # Początek pliku <- 
==============

```agda
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_)
```

---------------------

-> # Negacja <- 
==============

```agda
¬_ : Set → Set
¬ A = A → ⊥
```

```
infix 3 ¬_
```

---------------------

-> # Eliminacja i wprowadzenie negacji <- 
==============

```
¬-elim : ∀ {A : Set}
  → ¬ A
  → A
    ---
  → ⊥

¬¬-intro : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A

¬¬¬-elim : ∀ {A : Set}
  → ¬ ¬ ¬ A
    -------
  → ¬ A

contraposition : ∀ {A B : Set}
  → (A → B)
    -----------
  → (¬ B → ¬ A)
```


---------------------


-> # Przykłady <- 
==============



```
_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y  =  ¬ (x ≡ y)


_ : 1 ≢ 2


peano : ∀ {m : ℕ} → zero ≢ suc m
```

Dwa rodzaje identyczności na typie Void
```
id : ⊥ → ⊥
id x = x

id′ : ⊥ → ⊥
id′ ()


id≡id′ : id ≡ id′
id≡id′ = extensionality (λ())
```

---------------------


-> # Przykład <- 
==============


Mając typ reprezentujący nierówność ostrą udowodnić:

```
data _<_ : ℕ → ℕ → Set where
     0<s : ∀ { n } → 0 < suc n
     s<s : ∀ { m n } → m < n → suc m < suc n

nonrefl : ∀ { n } → ¬ (n < n)
```


---------------------


-> # Ćwiczenia <-
===============

Udowodnić:
```
¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
```

Pokazać, że każda z następujących własności implikuje pozostałe:

```
Excluded Middle: A ⊎ ¬ A, for all A
Double Negation Elimination: ¬ ¬ A → A, for all A
Peirce’s Law: ((A → B) → A) → A, for all A and B.
Implication as disjunction: (A → B) → ¬ A ⊎ B, for all A and B.
De Morgan: ¬ (¬ A × ¬ B) → A ⊎ B, for all A and B.
```

 
---------------------


-> # Kwantyfikatory: ogólny <-
================

Najpierw importy:

```
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
```

Kwantyfikator ogólny. Świadkiem na zajscie `∀ (x : A) → B x` jest: 
```
λ (x : A) → N x
```

Od razu mamy:
```
∀-elim : ∀ {A : Set} {B : A → Set}
  → (L : ∀ (x : A) → B x)
  → (M : A)
    -----------------
  → B M
∀-elim L M = L M
```

Ćwiczenia:
```
∀-distrib-× : ∀ {A : Set} {B C : A → Set} → (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} → (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x) → ∀ (x : A) → B x ⊎ C x
```


---------------------


-> # Kwantyfikatory: egzystencjalny <-
================

Rozważmy następujący typ:
```
data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B
```


Definiujemy lukier syntaktyczny:
```
Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → Bx) = Σ[ x ∈ A ] Bx
```
Czym się różni powyże od:

```
infix 2 Σ
syntax Σ A (λ x → Bx) = Σ[ x ∈ A ] Bx
```


W prostszej postaci:
```
∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B
```

---------------------

-> # Kwantyfikatory: własności <-
===============

```
∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
    ---------------
  → C

∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
```


---------------------


-> # Kwantyfikatory: zadania <-
===============

Zadanie 1. Udowodnić:
```
∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
    ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)

∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
    ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
```

Zadanie 2. Przypomnijmy:
```
data even : ℕ → Set
data odd  : ℕ → Set

data even where
  even-zero : even zero
  even-suc : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)
```
Udowodnić:
```
even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (    m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} →  odd n → ∃[ m ] (1 + m * 2 ≡ n)
∃-even : ∀ {n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) →  odd n
```

Zadanie 3. Udowodnić:
```
¬∃≃∀¬ : ∀ {A : Set} {B : A → Set}
  → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x
∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
    → ∃[ x ] (¬ B x)
      --------------
    → ¬ (∀ x → B x)
```
