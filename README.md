# Drzewa rozpinające na krawędź — dowód i odtworzenie obliczeń

Repozytorium zawiera kompletne wydanie 2.0.0 pracy **Filipa Majchrzaka** *Spanning trees per edge: a sharp bound and a question of Kenyon* oraz odrębny pakiet weryfikacyjny. Dla każdego skończonego multigrafu o m ≥ 1 krawędziach liczba drzew rozpinających τ spełnia **τ² · 8ᵐ < 27ᵐ**. Supremum τ^(1/m) po takich grafach wynosi **√(27/8)**. Publikacja obejmuje argument analityczny i drugi dowód sformalizowany w Lean 4. [Zenodo v2.0.0](https://doi.org/10.5281/zenodo.24523144) · [Oryginalny commit](https://github.com/kosza123/flow-certificate-thresholds/tree/b4c5b60f61766ea11cb7e72cc493181ac06f6c68)

| Chcę… | Punkt wejścia | Materiał kontrolny |
|---|---|---|
| Przeczytać pełny dowód | [Artykuł PDF](spanning-trees-per-edge/paper/spanning_trees_per_edge.pdf) | [Źródło LaTeX](spanning-trees-per-edge/paper/spanning_trees_per_edge.tex) |
| Prześledzić formalizację | [Mapa lematów i zależności](spanning-trees-per-edge/lean-kenyon/PROOF_ROUTE.md) | [Ograniczenie](spanning-trees-per-edge/lean-kenyon/Kenyon/Main.lean) · [Ostrość](spanning-trees-per-edge/lean-kenyon/Kenyon/Sharp.lean) |
| Sprawdzić autentyczność kopii wydania | [Kontroler](verify.py) | [ZIP z Zenodo](vendor/spanning-trees-per-edge-v2.0.0.zip) · [Indeks Git](github-tree-24523144.json) |
| Powtórzyć eksperymenty i enumerację | [Instrukcja odtworzenia](dokumentacja/odtworzenie.md) | [Skrypty autora](spanning-trees-per-edge/verify/) · [Niezależny rachunek](audyt/reproduce.py) · [Licznik drzew w C](audyt/count_trees.c) |
| Porównać własne wyniki | [Pełna tabela liczebności i maksimów](audyt/exact-results.txt) | [Zapis powtórzenia](audyt/odtworzenie.txt) · [Certyfikat i próba losowa](audyt/python-replay.txt) |
| Sprawdzić zakres audytu | [Raport matematyczny](dokumentacja/02-matematyka.md) · [Historia weryfikacji](dokumentacja/przebieg.md) | [Log kompilacji i aksjomatów](audyt/lean-replay.log) · [Kontrola jądra](audyt/kernel-direct.log) |
| Cytować lub ponownie wykorzystać pracę | [Opis autora i cytowanie](spanning-trees-per-edge/README.md) | [Apache 2.0](LICENSE) · [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/) |

Po sklonowaniu wykonaj z katalogu głównego `python -I -B verify.py`. Do tej kontroli wystarczy Python 3.12. Program porównuje wszystkie 76 plików z wydaniem Zenodo i identyfikatorami obiektów Git. Kolejne etapy opisuje instrukcja odtworzenia.

**Wynik audytu.** Dwa oryginalne eksperymenty dały wyjście zgodne wiersz po wierszu. W niezależnej enumeracji otrzymano 8 350 006 klas spójnych multigrafów bez pętli do 14 krawędzi po wyłączeniu drzew. Dla m=14 maksimum wyniosło 1280. Lokalne sprawdzenie formalizacji objęło 31 plików projektu, 39 raportów aksjomatów i 29 modułów sprawdzonych w jądrze. Pierwszeństwo naukowe i dokładna stała dla grafów planarnych pozostają odrębnymi pytaniami.

**Pochodzenie i licencje.** Katalog `spanning-trees-per-edge/` jest niezmienionym wydaniem autora. Kod i skrypty tego wydania mają licencję Apache 2.0, a tekst i ilustracje artykułu CC BY 4.0. Archiwum nauty 2.9.3 zachowuje własne pliki COPYRIGHT i LICENSE-2.0.txt. Pliki w `audyt/` dokumentują odrębne sprawdzenie. W kopii niezależnego skryptu reproduce.py dostosowano ścieżkę do tabeli referencyjnej do układu tego repozytorium.
