%title: Metody Formalne, wykład 3 
%author: Tomasz Brengos
%date: 2024-03-11



-> # Typ reprezentujący równość <- 
==============

```agda
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
```

ustalmy dodatkowo:

```agda
infix 4 _≡_
```

Własności:

```agda
sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong₂ : ∀ {A B C : Set} (f : A → B → C) {u x : A} {v y : B} → u ≡ x → v ≡ y → f u v ≡ f x y
subst : ∀ {A : Set} {x y : A} (P : A → Set) → x ≡ y → P x → P y
```

--------------------------------------------------


-> # Typ reprezentujący równość <- 
==============


```agda
module ≡-Reasoning {A : Set} where

  infix  1 begin_
  infixr 2 _≡⟨⟩_ step-≡
  infix  3 _∎

  begin_ : ∀ {x y : A} → x ≡ y → x ≡ y
  _≡⟨⟩_ : ∀ (x : A) {y : A} → x ≡ y → x ≡ y

  step-≡ : ∀ (x {y z} : A) → y ≡ z → x ≡ y → x ≡ z

  syntax step-≡ x y≡z x≡y  =  x ≡⟨  x≡y ⟩ y≡z

  _∎ : ∀ (x : A) → x ≡ x

open ≡-Reasoning
```

--------------------------------------------------


-> # Równość Leibniza <- 
==============

Definicja:

```agda
_≐_ : ∀ {A : Set} (x y : A) → Set₁
_≐_ {A} x y = ∀ (P : A → Set) → P x → P y
```

Własności:

```agda 
refl-≐ : ∀ {A : Set} {x : A} → x ≐ x
trans-≐ : ∀ {A : Set} {x y z : A} → x ≐ y → y ≐ z → x ≐ z
sym-≐ : ∀ {A : Set} {x y : A} → x ≐ y → y ≐ x

≡-implies-≐ : ∀ {A : Set} {x y : A}
  → x ≡ y
    -----
  → x ≐ y


≐-implies-≡ : ∀ {A : Set} {x y : A}
  → x ≐ y
    -----
  → x ≡ y
```


--------------------------------------------------


-> # Universe polymorphism <- 
==============


```agda
open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)
```

Importowane funkcje mają następujące typy:
```agda
lzero : Level
lsuc  : Level → Level
_⊔_ : Level → Level → Level

```
Ostatnia funkcja z powyższych to funkcja przyporządkowująca maksimum z dwóch wartości typu Level.


Nazwy Set₀, Set₁, Set₂, itd. są skrótami:

```agda
Set lzero
Set (lsuc lzero)
Set (lsuc (lsuc lzero))
```

Ogólna wersja typu równościowego:


```
data _≡′_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl′ : x ≡′ x
```

oraz wersja Leibniza:

```
_≐′_ : ∀ {ℓ : Level} {A : Set ℓ} (x y : A) → Set (lsuc ℓ)
_≐′_ {ℓ} {A} x y = ∀ (P : A → Set ℓ) → P x → P y
```
