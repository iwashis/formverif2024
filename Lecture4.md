%title: Metody Formalne, wykład 4 
%author: Tomasz Brengos
%date: 2024-03-18




-> # Część pierwsza wykładu <- 
==============


Lambda wyrażenia, rekordy i równoważność typów


--------------------------------------------------


-> # Importy, część pierwsza <- 
==============

Zaczynamy standardowo od importów w naszym nowym module:

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
```


--------------------------------------------------


-> # Wyrażenia lambda <- 
==============

Równoważne zapisy:

```agda
λ{ P1 → N1; ⋯ ; Pi → Ni }
```

oraz: 

```
f P1 = N1
⋯
f Pn = Nn
```

Składanie funkcji:


```agda
_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) x  = g (f x)
```

można równoważnie zapisać jako:


```agda
_∘′_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
g ∘′ f  =  λ x → g (f x)
```


--------------------------------------------------


-> # Extensionality <- 
==============

```agda 
postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g
```

Zdefiniujmy dodawanie inaczej:
```
_+′_ : ℕ → ℕ → ℕ
m +′ zero  = m
m +′ suc n = suc (m +′ n)
```
możemy łatwo udowodnić:
```
same-app : ∀ (m n : ℕ) → m +′ n ≡ m + n
```
Ponadto, używając aksjomatu ekstensjonalności dowodzimy:
```agda 
same : _+′_ ≡ _+_
```


Rozszerzony aksjomat ekstensjonalności:
```agda
postulate
  ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀(x : A) → B x}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g
```

--------------------------------------------------


-> # Izomorfizm <- 
==============


```agda
infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_
```

Powyższy zapis jest analogiczny do następującego:

```
data _≃′_ (A B : Set): Set where
  mk-≃′ : ∀ (to : A → B) →
          ∀ (from : B → A) →
          ∀ (from∘to : (∀ (x : A) → from (to x) ≡ x)) →
          ∀ (to∘from : (∀ (y : B) → to (from y) ≡ y)) →
          A ≃′ B
```

--------------------------------------------------


-> # Izomorfizm: własności <- 
==============

Uwaga notacyjna:
```
record
  { to    = f
  ; from  = g
  ; from∘to = g∘f
  ; to∘from = f∘g
  }
```

Teraz pokażmy pierwszych kilka stwierdzeń:
```
≃-refl : ∀ {A : Set}
    -----
  → A ≃ A
≃-sym : ∀ {A B : Set}
  → A ≃ B
    -----
  → B ≃ A

-- na ćwiczeniach:
≃-trans : ∀ {A B C : Set}
  → A ≃ B
  → B ≃ C
    -----
  → A ≃ C
```


--------------------------------------------------


-> # Ćwiczenia <- 
==============

```
≃-trans : ∀ {A B C : Set}
  → A ≃ B
  → B ≃ C
    -----
  → A ≃ C
```

Zdefiniować analogiczny typ danych dla relacji injekcji typów
```
infix 0 _≲_
record _≲_ (A B : Set) : Set where
```
oraz udowodnić:

```
≲-refl : ∀ {A : Set} → A ≲ A
≲-trans : ∀ {A B C : Set} → A ≲ B → B ≲ C → A ≲ C
≲-antisym : ∀ {A B : Set}
  → (A≲B : A ≲ B)
  → (B≲A : B ≲ A)
  → (to A≲B ≡ from B≲A)
  → (from A≲B ≡ to B≲A)
    -------------------
  → A ≃ B
```



--------------------------------------------------


-> # Praca domowa <- 
==============

Zdefiniujmy równoważność typów następująco: 
```
record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
```
Pokazać, że powyższa równoważność jest zwrotna, symetryczna i przechodnia.


--------------------------------------------------


-> # Część druga wykładu <- 
==============


Spójniki



--------------------------------------------------


-> # Importy, część druga <- 
==============

Stwóżmy nowy moduł (osoby plik) oraz zaimportujmy:
```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import plfa.part1.Isomorphism using (_≃_; _≲_; extensionality; _⇔_)
open plfa.part1.Isomorphism.≃-Reasoning

```

--------------------------------------------------


-> # Konjukcja jako operator produktowy <- 
==============


```agda
data _×_ (A B : Set) : Set where

```
```agda
proj₁ : ∀ {A B : Set}
  → A × B
    -----
  → A 
proj₂ : ∀ {A B : Set}
  → A × B
    -----
  → B
```

```agda
infixr 2 _×_
```

Możemy również zdefiniować produkt następująco:

```agda 
record _×′_ (A B : Set) : Set where
  constructor ⟨_,_⟩′
  field
    proj₁′ : A
    proj₂′ : B
open _×′_
```



--------------------------------------------------


-> # Własności produktu <- 
==============


```agda
×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
```

--------------------------------------------------


-> # Prawda jako typ o jednym świadku <- 
==============


```agda
data ⊤ : Set where
  tt : ⊤
```

Własności
```agda
⊤-count : ⊤ → ℕ
⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityʳ : ∀ {A : Set} → (A × ⊤) ≃ A
```

--------------------------------------------------


-> # Dysjunkcja jako suma rozłączna <- 
==============


```
data _⊎_ (A B : Set) : Set where

  inj₁ :
      A
      -----
    → A ⊎ B

  inj₂ :
      B
      -----
    → A ⊎ B
```

```
case-⊎ : ∀ {A B C : Set}
  → (A → C)
  → (B → C)
  → A ⊎ B
    -----------
  → C
η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) →
  case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w

infixr 1 _⊎_
```


--------------------------------------------------


-> # Fałsz, czyli typ bez świadków <- 
==============



```agda
data ⊥ : Set where
```

Własności:

```
⊥-elim : ∀ {A : Set}
  → ⊥
    --
  → A  


uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w

```

--------------------------------------------------

-> # Implikacja to funkcja <- 
==============



```agda
→-elim : ∀ {A B : Set}
  → (A → B)
  → A
    -------
  → B
```

Własność:

```
currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
```

--------------------------------------------------


-> # Praca domowa <- 
==============

1. Pokazać, że `A ⇔ B` jest równoważne `(A → B) × (B → A)`.
2. Pokazać łączność i przemienność `_⊎_` (z dokładnością do izomorfizmu).
3. Pokazać rozdzielność `→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))`
4. Pokazać rozdzielność `→-distrib-× : ∀ {A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)`
5. Pokazać rozdzielność `×-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)`

