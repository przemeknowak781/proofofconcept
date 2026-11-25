# Odtworzenie z czystego klonu

**Autorem odtwarzanego dowodu jest Filip Majchrzak.** [Publikacja źródłowa, wydanie 2.0.0](https://doi.org/10.5281/zenodo.24523144)

Wymagania do całości to Python 3.12 (w lokalnym przebiegu 3.12.10), Git, Bash, make, kompilator C oraz elan/Lake dla Lean. Kroki 1–3 można wykonać bez Lean. Wszystkie polecenia zaczynają się w katalogu głównym repozytorium; polecenia powłoki w blokach sh zakładają system POSIX. Dla Windows podano oddzielny wariant generatorów.

## 1. Sprawdzenie wejść

```sh
git clone https://github.com/przemeknowak781/proofofconcept.git
cd proofofconcept
git rev-parse HEAD
python3 -I -B verify.py
```

Zapisz commit wraz z własnym wynikiem. Kontroler sprawdza MD5 ZIP zgodny z metadanymi Zenodo, komplet 76 plików oraz ich identyfikatory Git z oryginalnej rewizji. Dodatkowo w systemie z GNU coreutils można wykonać `sha256sum -c SHA256SUMS` dla wszystkich opublikowanych plików poza samym manifestem. Potwierdzeniem pochodzenia z niezależnego źródła jest porównanie z [depozytem Zenodo](https://zenodo.org/records/24523144).

## 2. Certyfikat i próba losowa

```sh
python3 -m venv .venv
. .venv/bin/activate
python -m pip install -r requirements.txt
python -I -B verify.py --numbers
```

Na Windows aktywuj środowisko przez `.\.venv\Scripts\Activate.ps1` lub użyj bezpośrednio jego python.exe. Skrypt sprawdza certyfikat przedziałowy, powtarza próbę 300 grafów z ziarnem 3, porównuje wyjście z plikami autora, wykonuje 468 porównań na ułamkach i porównuje liczby klas z rachunkiem Burnside’a. NumPy i mpmath są przypięte. Porównanie próby losowej jest wrażliwe na różnice reprezentacji ostatnich cyfr między platformami. Do diagnozy wywołaj oddzielnie `python spanning-trees-per-edge/verify/check_class.py 3 300` i porównaj z sąsiednim plikiem .out.

## 3. Wszystkie klasy i liczba drzew

```sh
mkdir -p build/bin
tar -xzf vendor/nauty2_9_3.tar.gz -C build
(cd build/nauty2_9_3 && ./configure && make geng multig)
cp build/nauty2_9_3/geng build/nauty2_9_3/multig build/bin/
cc -std=c11 -O2 audyt/count_trees.c -o build/bin/count_trees
python -I -B verify.py --bin build/bin
```

Na Windows ten sam kontroler przyjmuje ścieżkę do katalogu zawierającego geng.exe, multig.exe i count_trees.exe. Lokalny przebieg wykonano w ten sposób z zachowanymi generatorami nauty 2.9.3. Skrypt sprawdza statusy procesów, liczność każdej pary (n,m), maksima i zgodność z zachowaną tabelą. Oczekiwane ostatnie wiersze:

```text
14 6534218 6534218 1280
Total: 8350006
```

## 4. Sprawdzenie dowodu ogólnego w Lean

Z zainstalowanym elan i dostępem do sieci przy pierwszym pobieraniu zależności:

```sh
cd spanning-trees-per-edge/lean-kenyon
lake env lean --version
lake exe cache get
bash scripts/check.sh
```

Pakiet wskazuje Lean 4.37.0-rc1 i Mathlib 53dad9ed98be8416b6ca1111e55a03de4303231f. Pobranie zależności i cache wymaga kilku GB. Skrypt autora buduje pakiet, skanuje źródła, analizuje listy aksjomatów i uruchamia leanchecker. Oczekiwany finał to `OK: build, 39 axiom reports, kernel replay of 29 modules`. Dodatkowa ścieżka odtworzenia lokalnej kontroli z tego samego katalogu po zbudowaniu modułów:

```sh
lake env lean scripts/PrintAxioms.lean
lake env lean ../../replay_modules.lean
```

Druga komenda powinna wypisać 29 wierszy kernel OK. Zestaw wynik z [logiem audytu](../audyt/kernel-direct.log). Alternatywny [skrypt przebudowy](../audyt/replay_lean.py) można uruchomić poleceniem `lake env python3 -I -X utf8 ../../audyt/replay_lean.py`. Przebudowuje moduły, analizuje aksjomaty i wykonuje osobny proces sprawdzający dla każdego modułu oraz kontrolę ujemną. Zachowany lokalny log kończy się w czasie tej wolniejszej pętli; ukończony przebieg wszystkich 29 modułów dokumentuje log wersji jednoprocesowej. [Protokół czystego odtworzenia autora](../spanning-trees-per-edge/lean-kenyon/VERIFICATION_CLEANROOM.txt)
