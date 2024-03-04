Ogólne uwagi: Projekt oddany być musi przez załączenie do niego publicznego repozytorium,
wraz z pełną historią commitów wszystkich studentów w grupie. Projekt należy uzupełnić o plik README.md 
w którym przedstawione zostaną pełne wymagania do uruchomienia go. Kod należy w bardzo dokładny sposób 
komentować.

Tematy: 
1. Verified compilation:
    Rozdział 17 z książki (17.4):
    Dane są dwa języki:
    L1: Commands c :: Return v |x <- c; c|Loop i f |Read n|Write n n

    L2: Expressions e :: x | n |e + e| *{e}
    Statements s :: skip |x <- e |*{e} <- e | s;s |if e then s else s|while e do s
    
    Zdefiniować dla nich small-step semantics (patrz książka), tłumaczenie, oraz udowodnić
    zgodność tłumaczenia z semantyką.

2. Hoare logic:
    Dla imperatrywnego języka z pamięcią (patrz rodział 14):
    Numbers n in N
    Variables x in String 
    Expressions e :: n | x | e + e |  e - e |  e * e | *{e}  
    Booleanexpressions b :: e = e | e < e 
    Commands c :: skip | x <- e | *{e} <- e | c ; c | if b then c else c | {a}while b do c | assert(a)
    
    zdefiniować big-step semantics. Ponadto, wprowadzić trójki Hoare'a i udowodnić zgodność logiki 
    Hoare'a (Tw. 14.2).

3. Verified compilation 2: 
    Certyfikowana kompilacja z języka prostych wyrażeń arytmetycznych do zabawkowego języka assembler.

4. Certyfikowana złożoność kilku wybranych funkcji
    (https://projekter.aau.dk/projekter/files/335444832/pt101f20thesis.pdf)

5. Safety i liveness prostych programów równoległych
    (https://odr.chalmers.se/server/api/core/bitstreams/92c45899-9264-451e-bb12-c97f06938ed1/content)

6. Formalizacja uproszczonego modelu sieci Bitcoin:
    (https://repositorio.fgv.br/server/api/core/bitstreams/3d0e0572-2fcd-4d89-88b5-422bcb231789/content)






