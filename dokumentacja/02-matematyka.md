# Co dokładnie sprawdziliśmy

**Autorem dowodu jest Filip Majchrzak.** Poniższy raport dokumentuje sprawdzenie jego twierdzenia i obliczeń. [Oryginalna praca](https://doi.org/10.5281/zenodo.24523144)

Niech m ≥ 1 będzie liczbą krawędzi skończonego multigrafu G, a τ(G) liczbą jego drzew rozpinających. Formalizacja v2 dowodzi **τ(G)² · 8ᵐ < 27ᵐ**. Dla każdego 0 < c < 27/8 istnieje graf z cᵐ < τ(G)². Razem daje to **sup τ(G)^(1/m) = √(27/8)**. Ścisła nierówność oznacza, że żaden pojedynczy skończony graf o dodatniej liczbie krawędzi nie osiąga supremum.

| Kontrola | Metoda i wynik | Ślad |
|---|---|---|
| Certyfikat przedziałowy | mpmath.iv z precyzją 60 cyfr. Ocena kandydatów na maksima oraz porównanie stałych. Wynik końcowy ALL CERTIFIED. | `verify/certify_intervals.py` i odpowiadający .out w wydaniu |
| Spójność numeryczna | 300 grafów klasy C, ziarno 3, w tym 190 z wierzchołkiem stopnia 2. Maksymalna różnica między wzorem i całką 4,22·10⁻¹⁴, defekt tożsamości 3,55·10⁻¹⁵. | `audyt/python-replay.txt` |
| Tablica pomocnicza | 468 porównań po usunięciu logarytmów przez potęgowanie i przejściu na ułamki. Dla d=4 i r=1/8 dokładna równość. Celowo za mocny warunek dla d=5 został wykryty. | `table_check` w `audyt/reproduce.py` |
| Kompletność enumeracji | geng generuje spójne proste nośniki. multig nadaje krotności. Liczbę klas dla każdej pary (n,m) sprawdzono odrębnym rachunkiem Burnside’a z usunięciem grafów niespójnych. | `connected_counts` i `run_for_n` |
| Liczba drzew | Wyznacznik kofaktora laplasjanu z twierdzenia Kirchhoffa, liczony modulo 65521. Liczba możliwych podzbiorów krawędzi ≤ 2¹⁴ < 65521, więc reszta daje dokładną liczbę. | `audyt/count_trees.c` |
| Niezależne ograniczenie dla małych m | Z iloczynu niezerowych wartości własnych i AM–GM wynika τ ≤ (2m/(n−1))^(n−1)/n. Porównanie całkowitoliczbowe sprawdzono dla m=1,…,14 i n=2,…,m+1. | `spectral_check` |

**Zakres liczby 8 350 006.** Jest to liczba klas izomorfizmu spójnych multigrafów bez pętli do 14 krawędzi po pominięciu drzew. Drzewo ma τ=1, graf niespójny ma τ=0, a pętla nie może należeć do drzewa rozpinającego. Dla samego m=14 uzyskano 6 534 218 klas i maksimum τ=1280. Przykładem jest K₄,₄ po usunięciu dwóch krawędzi o rozłącznych końcach. Pierwotny raport odnotowuje również bezpośrednie policzenie podzbiorów siedmiokrawędziowych. Pełne wiersze dla m=2,…,14 są w [exact-results.txt](../audyt/exact-results.txt).

**Zakres weryfikacji formalnej.** W `Kenyon/Forest.lean` definicja `numTrees` liczy spójne podzbiory krawędzi o liczności n−1, rozróżniając krawędzie równoległe. Sprawdzono `kenyon_bound` i `kenyon_sharp` oraz ich zależności. Przebudowano 31 plików (29 modułów z deklaracjami i dwa moduły importujące). Dla wszystkich 39 raportowanych twierdzeń użyte aksjomaty należą do zbioru `propext`, `Classical.choice`, `Quot.sound`. W kontroli jądra `replayFromImports` zakończyło sprawdzanie wszystkich 29 modułów. Zależności Mathlib wczytano z cache. Lista kroków matematycznych znajduje się w [PROOF_ROUTE.md](../spanning-trees-per-edge/lean-kenyon/PROOF_ROUTE.md).

**Granice wniosku.** Dowód w Lean dotyczy drugiego argumentu publikacji. Próba losowa i enumeracja sprawdzają konkretne przypadki. Pierwszy argument analityczny nie przeszedł tutaj osobnej recenzji każdego lematu. Nie wyznaczono dokładnego supremum planarnego ani grafów maksymalnych dla wszystkich m. Ustalenie pierwszeństwa wymaga odrębnej kwerendy.
