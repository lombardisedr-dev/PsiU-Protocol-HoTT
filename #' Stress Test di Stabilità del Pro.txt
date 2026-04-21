name: PSIU_Runner

on:
  push:
    branches: [ main ]
  workflow_dispatch:

jobs:
  execute:
    runs-on: ubuntu-latest
    steps:
      - name: Checkout code
        uses: actions/checkout@v4

      - name: Setup R
        uses: r-lib/actions/setup-r@v2

      - name: Run Protocol
        run: |
          # Questo comando stampa i file presenti (per debug) e carica tutto
          Rscript -e 'print(list.files()); files <- list.files(pattern = "\\.[rR]$"); if(length(files) > 0) { lapply(files, source); stress_test(10000) } else { stop("ERRORE: Nessun file .R trovato nel repository!") }'

