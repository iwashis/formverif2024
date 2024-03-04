%title: Metody Formalne, wykład 2 
%author: Tomasz Brengos
%date: 2024-03-04


-> # Początek pliku <- 
==============

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm; +-identityʳ)

```


--------------------------------------------------


-> # Typ reprezentujący częściowy porządek na liczbach naturalnych <- 
==============

```agda
data _≤_ : ℕ → ℕ → Set where
 ...
```
pierwszy dowod:
```agda
_ : 2 ≤ 4 
_ = ?
```
mamy następujące twierdzenia:

```
inv-s≤s : ∀ {m n : ℕ} → suc m ≤ suc n → m ≤ n
```
oraz:
```
inv-z≤n : ∀ {m : ℕ} → m ≤ zero → m ≡ zero
```

--------------------------------------------------

-> # Total order <- 
==============

```agda
data Total (m n : ℕ) : Set where

  forward :
      m ≤ n
      ---------
    → Total m n

  flipped :
      n ≤ m
      ---------
    → Total m n
```

porównajmy z:


```agda
data Total′ : ℕ → ℕ → Set where

  forward′ : ∀ {m n : ℕ}
    → m ≤ n
      ----------
    → Total′ m n

  flipped′ : ∀ {m n : ℕ}
    → n ≤ m
      ----------
    → Total′ m n
```

-------------------------------------------------

-> # Słowo klucz with <- 
=========================

```agda
≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero    n                         =  forward z≤n
≤-total (suc m) zero                      =  flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...                        | forward m≤n  =  forward (s≤s m≤n)
...                        | flipped n≤m  =  flipped (s≤s n≤m)
```

to co wyżej jest równoważne:

```agda
≤-total′ : ∀ (m n : ℕ) → Total m n
≤-total′ zero    n        =  forward z≤n
≤-total′ (suc m) zero     =  flipped z≤n
≤-total′ (suc m) (suc n)  =  helper (≤-total′ m n)
  where
  helper : Total m n → Total (suc m) (suc n)
  helper (forward m≤n)  =  forward (s≤s m≤n)
  helper (flipped n≤m)  =  flipped (s≤s n≤m)
```

-------------------------------------------------

-> # Słowo klucz rewrite <- 
=========================

Choć na poprzednim wykładzie istniały już potencjalne zastosowania 
słowa klucza `rewrite`, wprowadzamy je w przypadku dowodu monotoniczności:

Prawa monotoniczność dodawania:

```agda 
+-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → n + p ≤ n + q
+-monoʳ-≤ zero    p q p≤q  =  p≤q
+-monoʳ-≤ (suc n) p q p≤q  =  s≤s (+-monoʳ-≤ n p q p≤q)
```

Lewa monotoniczność:

```agda 
+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n  rewrite +-comm m p | +-comm n p  = +-monoʳ-≤ p m n m≤n
```

Ćwiczenie: przepisać niektóre dowody z poprzedniego wykładu używając słowa klucza 
`rewrite`.

-------------------------------------------------

-> Rewrite w dowodach z `even` oraz `odd` <-
=========================
Dla odpowiednio zdefiniowanych typów `even` oraz `odd` mamy:

```agda 
even-comm : ∀ (m n : ℕ)
  → even (m + n)
    ------------
  → even (n + m)
even-comm m n ev  rewrite +-comm n m  =  ev
```

Ćwiczenie: przeprowadzić rozmowowanie dotyczące dowodu powyższego
twierdzenia krok po kroku.

------------------------------------------------

-> Rewrite w innych dowodach <-
=========================
Wracając do jednego z przykładów z poprzedniego wykładu

```agda
+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ zero    n  rewrite +-identity n             =  refl
+-comm′ (suc m) n  rewrite +-suc n m | +-comm' m n  =  refl
```

------------------------------------------------

-> Notacja Rewrite: syntaktyczny lukier `with` <-
=========================

Fragment kodu:

```agda
even-comm : ∀ (m n : ℕ)
  → even (m + n)
    ------------
  → even (n + m)
even-comm m n ev  rewrite +-comm n m  =  ev
```

jest równoważny: 

```agda 
even-comm′ : ∀ (m n : ℕ)
  → even (m + n)
    ------------
  → even (n + m)
even-comm′ m n ev with   m + n  | +-comm m n
...                  | .(n + m) | refl       = ev
```
