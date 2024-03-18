## Ogólne uwagi:
Projekt oddany być musi przez załączenie do niego publicznego repozytorium, wraz z pełną historią commitów wszystkich studentów w grupie. Projekt należy uzupełnić o plik `README.md` w którym przedstawione zostaną pełne wymagania do uruchomienia go. Kod należy w bardzo dokładny sposób komentować.

## Tematy:
1. **Verified compilation:**
   - Rozdział 17 z książki (17.4) (C):
     - Dane są dwa języki:
       - `L1: Commands c :: Return v |x <- c; c|Loop i f |Read n|Write n n`
       - `L2: Expressions e :: x | n |e + e| *{e}`
       - `Statements s :: skip |x <- e |*{e} <- e | s;s |if e then s else s|while e do s`
     - Zdefiniować dla nich small-step semantics (patrz książka), tłumaczenie, oraz udowodnić zgodność tłumaczenia z semantyką.
    (rezerwacja B, KS, JS)    

2. **Hoare logic (C):**
   - Dla imperatrywnego języka z pamięcią (patrz rodział 14):
     - `Numbers n in N`
     - `Variables x in String`
     - `Expressions e :: n | x | e + e |  e - e |  e * e | *{e}`
     - `Booleanexpressions b :: e = e | e < e`
     - `Commands c :: skip | x <- e | *{e} <- e | c ; c | if b then c else c | {a}while b do c | assert(a)`
   - zdefiniować big-step semantics. Ponadto, wprowadzić trójki Hoare'a i udowodnić zgodność logiki Hoare'a (Tw. 14.2).

3. **Verified compilation 2:**
   - Certyfikowana kompilacja z języka prostych wyrażeń arytmetycznych 
    `U ::=  n | U + U | U * U`
    do zabawkowego języka assambler:
    ```
    Prog  ::= Begin;A
    A     ::= Opper;A | End
    Opper ::= Set n | Load x | Store x | Add x | Mul x

    ```
    (rezerwacja SM, ZM)

4. **Certyfikowana złożoność kilku wybranych funkcji (A)**
   - [https://projekter.aau.dk/projekter/files/335444832/pt101f20thesis.pdf](https://projekter.aau.dk/projekter/files/335444832/pt101f20thesis.pdf)

5. **Safety i liveness prostych programów równoległych (A)**
   - [https://odr.chalmers.se/server/api/core/bitstreams/92c45899-9264-451e-bb12-c97f06938ed1/content](https://odr.chalmers.se/server/api/core/bitstreams/92c45899-9264-451e-bb12-c97f06938ed1/content)
   (rezerwacja DS, PL)

6. **Formalizacja uproszczonego modelu sieci Bitcoin (A):**
   - [https://repositorio.fgv.br/server/api/core/bitstreams/3d0e0572-2fcd-4d89-88b5-422bcb231789/content](https://repositorio.fgv.br/server/api/core/bitstreams/3d0e0572-2fcd-4d89-88b5-422bcb231789/content)

   (rezerwacja JD, KL, OW)

7. **Formalizacja Simplified Calculus of Communicating Systems**
   - [http://www.lfcs.inf.ed.ac.uk/reports/86/ECS-LFCS-86-7/ECS-LFCS-86-7.pdf](http://www.lfcs.inf.ed.ac.uk/reports/86/ECS-LFCS-86-7/ECS-LFCS-86-7.pdf)

8. **Formalizacja logiki rachunku zdań (pełność i zgodność)**:
    - [https://akaposi.github.io/proplogic.pdf]
    (rezerwacja KB, AW, ZB)

