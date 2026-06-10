# --- 1. CARICAMENTO LOCALE (Anti-Errore Action) ---
# Installiamo il pacchetto dai file del repository invece che da CRAN
if (!requireNamespace("PsiUEngineRL", quietly = TRUE)) {
  install.packages(".", repos = NULL, type = "source")
}
library(PsiUEngineRL)
library(testthat)

G <- 0.6180339887
set.seed(2026)

# --- 2. IL TEST DI DISCRIMINAZIONE ---
# Scenario: Ordine (sd=0.001) vs Caos (sd=0.08)
res_clean <- PsiU_Engine_RL(G + rnorm(2000, sd = 0.001))
res_noisy <- PsiU_Engine_RL(G + rnorm(2000, sd = 0.08))

ratio_clean <- sum(res_clean$Stato_Modale == "BOX (Necessity) [□]") / 2000
ratio_noisy <- sum(res_noisy$Stato_Modale == "BOX (Necessity) [□]") / 2000

# --- 3. CERTIFICAZIONE ---
test_that("Il motore distingue correttamente ordine e caos", {
  # Deve esserci una differenza netta (il motore declassa il caos)
  expect_gt(ratio_clean, 0.85) # Ordine riconosciuto
  expect_lt(ratio_noisy, 0.15) # Caos scartato
})

cat("\n[SUCCESS] Topologia validata: il motore non si lascia ingannare dal rumore.\n")
