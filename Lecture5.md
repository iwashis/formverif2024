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

Udowodnić (do domu):
```
¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
```

(Do domu) 
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

Zadanie 1 (do domu). Udowodnić:
```
∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
    ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)

∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
    ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
```


---------------------


-> # Kwantyfikatory: zadania <-
===============


Zadanie 2 (zrobione na zajęciach). Przypomnijmy:
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

---------------------


-> # Kwantyfikatory: zadania <-
===============


Udowodnić (dwa ostatnie do domu):
```
even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (    m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} →  odd n → ∃[ m ] (1 + m * 2 ≡ n)
∃-even : ∀ {n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) →  odd n
```


---------------------


-> # Kwantyfikatory: zadania <-
===============



Zadanie 3 (do domu). Udowodnić:
```
¬∃≃∀¬ : ∀ {A : Set} {B : A → Set}
  → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x
∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
    → ∃[ x ] (¬ B x)
      --------------
    → ¬ (∀ x → B x)
```


---------------------


-> # Wartości Boole'owskie i rozstrzygalność <-
===============

Importy:
```
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using ()
  renaming (contradiction to ¬¬-intro)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
```



---------------------


-> # Wartości Boole'owskie i rozstrzygalność <-
===============


Przypomnijmy:
```
infix 4 _≤_

data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ}
      --------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      -------------
    → suc m ≤ suc n
```
gdzie mamy:
```
2≤4 : 2 ≤ 4
2≤4 = s≤s (s≤s z≤n)

¬4≤2 : ¬ (4 ≤ 2)
¬4≤2 (s≤s (s≤s ()))
```

---------------------


-> # Wartości Boole'owskie i rozstrzygalność <-
===============


Ale można też tak:

```
data Bool : Set where
  true  : Bool
  false : Bool

infix 4 _≤ᵇ_

_≤ᵇ_ : ℕ → ℕ → Bool
zero ≤ᵇ n       =  true
suc m ≤ᵇ zero   =  false
suc m ≤ᵇ suc n  =  m ≤ᵇ n
```

---------------------

-> # Łączenie świadków z obliczeniami <-
===============

```
T : Bool → Set
T true   =  ⊤
T false  =  ⊥

T→≡ : ∀ (b : Bool) → T b → b ≡ true
≡→T : ∀ {b : Bool} → b ≡ true → T b
```

Możemy udowodnić:


```
≤ᵇ→≤ : ∀ (m n : ℕ) → T (m ≤ᵇ n) → m ≤ n
≤→≤ᵇ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ n)
```
---------------------

-> # Łączenie świadków z obliczeniami <-
===============


Zdefiniujmy:
```
data Dec (A : Set) : Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A
```
Przypomnijmy sobie:
```
¬s≤z : ∀ {m : ℕ} → ¬ (suc m ≤ zero)
¬s≤z ()

¬s≤s : ∀ {m n : ℕ} → ¬ (m ≤ n) → ¬ (suc m ≤ suc n)
¬s≤s ¬m≤n (s≤s m≤n) = ¬m≤n m≤n
```
oraz pokażmy:
```
_≤?_ : ∀ (m n : ℕ) → Dec (m ≤ n)
```
Ponadto, możemy powyższe pokazać następująco:
```
_≤?′_ : ∀ (m n : ℕ) → Dec (m ≤ n)
m ≤?′ n with m ≤ᵇ n | ≤ᵇ→≤ m n | ≤→≤ᵇ {m} {n}
...        | true   | p        | _            = yes (p tt)
...        | false  | _        | ¬p           = no ¬p
```


--------------------

-> # Łączenie świadków z obliczeniami <-
===============


Zdefiniujmy:
```
⌊_⌋ : ∀ {A : Set} → Dec A → Bool
⌊ yes x ⌋  =  true
⌊ no ¬x ⌋  =  false
```
Wtedy mamy:
```
_≤ᵇ′_ : ℕ → ℕ → Bool
m ≤ᵇ′ n  =  ⌊ m ≤? n ⌋
```

Ponadto, mamy:
```
toWitness : ∀ {A : Set} {D : Dec A} → T ⌊ D ⌋ → A
fromWitness : ∀ {A : Set} {D : Dec A} → A → T ⌊ D ⌋
```
Wtedy:
```
≤ᵇ′→≤ : ∀ {m n : ℕ} → T (m ≤ᵇ′ n) → m ≤ n
≤ᵇ′→≤  =  toWitness

≤→≤ᵇ′ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ′ n)
≤→≤ᵇ′  =  fromWitness
```
